using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Security.Cryptography;
using System.Text;
using System.Threading;
using Bencodex;
using Bencodex.Types;
using Libplanet.Action;
using Libplanet.Store.Trie;
using Libplanet.Tx;

namespace Libplanet.Blocks
{
    [Equals]
    public class Block<T> : IBlockExcerpt
        where T : IAction, new()
    {
        /// <summary>
        /// The most latest protocol version.
        /// </summary>
        public const int CurrentProtocolVersion = BlockHeader.CurrentProtocolVersion;

        private int? _bytesLength = null;
        private BlockHeader? _header = null;
        private BlockHash? _preEvaluationHash = null;
        private BlockHash? _hash = null;

        /// <summary>
        /// Creates a <see cref="Block{T}"/> instance by manually filling field values.
        /// For a more automated way, see also the <see cref="Mine"/> method.
        /// </summary>
        /// <param name="index">The height of the block to create.  Goes to the <see cref="Index"/>.
        /// </param>
        /// <param name="difficulty">The mining difficulty that <paramref name="nonce"/> has to
        /// satisfy.  Goes to the <see cref="Difficulty"/>.</param>
        /// <param name="totalDifficulty">The total mining difficulty until this block.
        /// See also <see cref="Difficulty"/>.</param>
        /// <param name="nonce">The nonce which satisfy the given <paramref name="difficulty"/> with
        /// any other field values.  Goes to the <see cref="Nonce"/>.</param>
        /// <param name="miner">An optional address refers to who mines this block.
        /// Goes to the <see cref="Miner"/>.</param>
        /// <param name="previousHash">The previous block's <see cref="Hash"/>.  If it's a genesis
        /// block (i.e., <paramref name="index"/> is 0) this should be <c>null</c>.
        /// Goes to the <see cref="PreviousHash"/>.</param>
        /// <param name="timestamp">The time this block is created.  Goes to
        /// the <see cref="Timestamp"/>.</param>
        /// <param name="transactions">The transactions to be mined together with this block.
        /// Transactions become sorted in an unpredicted-before-mined order and then go to
        /// the <see cref="Transactions"/> property.
        /// </param>
        /// <param name="preEvaluationHash">The hash derived from the block <em>except of</em>
        /// <paramref name="stateRootHash"/> (i.e., without action evaluation).
        /// Automatically determined if <c>null</c> is passed (which is default).</param>
        /// <param name="stateRootHash">The <see cref="ITrie.Hash"/> of the states on the block.
        /// </param>
        /// <param name="protocolVersion">The protocol version. <see cref="CurrentProtocolVersion"/>
        /// by default.</param>
        /// <remarks>
        /// Due to historic reasons, there is non-trivial implicit logic embedded inside this
        /// constructor.  It is strongly recommended to use <see cref="Mine"/> instead.
        /// </remarks>
        /// <seealso cref="Mine"/>
        public Block(
            long index,
            long difficulty,
            BigInteger totalDifficulty,
            Nonce nonce,
            Address? miner,
            BlockHash? previousHash,
            DateTimeOffset timestamp,
            IReadOnlyList<Transaction<T>> transactions,
            BlockHash? preEvaluationHash = null,
            HashDigest<SHA256>? stateRootHash = null,
            int protocolVersion = CurrentProtocolVersion)
        {
            // FIXME: Calling with preEvaluationHash not null and stateRootHash null should
            // also be invalid under normal circumstances.  There should be a constructor
            // explicitly filling in all fields without implicit logic to accomodate
            // existing tests.
            if (preEvaluationHash is null && !(stateRootHash is null))
            {
                throw new ArgumentException(
                    "If preEvaluationHash is null, stateRootHash must also be null.");
            }

            ProtocolVersion = protocolVersion;
            Index = index;
            Difficulty = difficulty;
            TotalDifficulty = totalDifficulty;
            Nonce = nonce;
            Miner = miner;
            PreviousHash = previousHash;
            Timestamp = timestamp;
            Transactions = transactions.OrderBy(tx => tx.Id).ToArray();
            TxHash = CalculateTxHashes(Transactions);

            if (preEvaluationHash is { } preEvaluationBlockHash)
            {
                _preEvaluationHash = preEvaluationBlockHash;
                StateRootHash = stateRootHash;
                _hash = Hashcash.Hash(Header.SerializeForHash());
            }
            else
            {
                // FIXME: This only works due to sanity constraint on usage.
                _preEvaluationHash = Hashcash.Hash(Header.SerializeForPreEvaluationHash());
                StateRootHash = stateRootHash;
                _hash = _preEvaluationHash;
            }

            // As the order of transactions should be unpredictable until a block is mined,
            // the sorter key should be derived from both a block hash and a txid.
            var hashInteger = new BigInteger(PreEvaluationHash.ToByteArray());

            // If there are multiple transactions for the same signer these should be ordered by
            // their tx nonces.  So transactions of the same signer should have the same sort key.
            // The following logic "flattens" multiple tx ids having the same signer into a single
            // txid by applying XOR between them.
            IImmutableDictionary<Address, IImmutableSet<Transaction<T>>> signerTxs = Transactions
                .GroupBy(tx => tx.Signer)
                .ToImmutableDictionary(
                    g => g.Key,
                    g => (IImmutableSet<Transaction<T>>)g.ToImmutableHashSet()
                );
            IImmutableDictionary<Address, BigInteger> signerTxIds = signerTxs
                .ToImmutableDictionary(
                    pair => pair.Key,
                    pair => pair.Value
                        .Select(tx => new BigInteger(tx.Id.ToByteArray()))
                        .OrderBy(txid => txid)
                        .Aggregate((a, b) => a ^ b)
                );

            // Order signers by values derivied from both block hash and their "flatten" txid:
            IImmutableList<Address> signers = signerTxIds
                .OrderBy(pair => pair.Value ^ hashInteger)
                .Select(pair => pair.Key)
                .ToImmutableArray();

            // Order transactions for each signer by their tx nonces:
            Transactions = signers
                .SelectMany(signer => signerTxs[signer].OrderBy(tx => tx.Nonce))
                .ToImmutableArray();
        }

        /// <summary>
        /// Creates a <see cref="Block{T}"/> instance from its serialization.
        /// </summary>
        /// <param name="dict">The <see cref="Bencodex.Types.Dictionary"/>
        /// representation of <see cref="Block{T}"/> instance.
        /// </param>
        public Block(Bencodex.Types.Dictionary dict)
            : this(new RawBlock(dict))
        {
        }

        // FIXME: Should this necessarily be a public constructor?
        // See also <https://github.com/planetarium/libplanet/issues/1146>.
        public Block(
            Block<T> block,
            HashDigest<SHA256>? stateRootHash
        )
            : this(
                block.Index,
                block.Difficulty,
                block.TotalDifficulty,
                block.Nonce,
                block.Miner,
                block.PreviousHash,
                block.Timestamp,
                block.Transactions,
                block.PreEvaluationHash,
                stateRootHash,
                protocolVersion: block.ProtocolVersion)
        {
        }

        private Block(RawBlock rawBlock)
        {
            _header = rawBlock.Header;

            ProtocolVersion = Header.ProtocolVersion;
            Index = Header.Index;
            Difficulty = Header.Difficulty;
            TotalDifficulty = Header.TotalDifficulty;
            Nonce = new Nonce(Header.Nonce.ToArray());
            Miner = Header.Miner.Any()
                ? new Address(Header.Miner)
                : (Address?)null;
            PreviousHash = Header.PreviousHash.Any()
                ? new BlockHash(Header.PreviousHash)
                : (BlockHash?)null;
            Timestamp = DateTimeOffset.ParseExact(
                Header.Timestamp,
                BlockHeader.TimestampFormat,
                CultureInfo.InvariantCulture).ToUniversalTime();
            TxHash = Header.TxHash.Any()
                ? new HashDigest<SHA256>(rawBlock.Header.TxHash)
                : (HashDigest<SHA256>?)null;

            // FIXME: Transactions should be re-ordered to properly validate StateRootHash.
            // See also <https://github.com/planetarium/libplanet/issues/1299>.
            Transactions = rawBlock.Transactions
                .Select(tx => Transaction<T>.Deserialize(tx.ToArray(), false))
                .ToImmutableList();

            _preEvaluationHash = rawBlock.Header.PreEvaluationHash.Any()
                ? new BlockHash(rawBlock.Header.PreEvaluationHash)
                : throw new ArgumentException(nameof(rawBlock.Header));

            // FIXME: we should convert `StateRootHash`'s type to `HashDisgest<SHA256>` after
            // removing `IBlockStateStore`.
            // See also <https://github.com/planetarium/libplanet/pull/1116#discussion_r535836480>.
            StateRootHash = rawBlock.Header.StateRootHash.Any()
                ? new HashDigest<SHA256>(rawBlock.Header.StateRootHash)
                : (HashDigest<SHA256>?)null;
            _hash = new BlockHash(rawBlock.Header.Hash);
        }

        /// <summary>
        /// The protocol version number.
        /// </summary>
        [IgnoreDuringEquals]
        public int ProtocolVersion { get; }

        /// <summary>
        /// <see cref="Hash"/> is derived from a serialized <see cref="Block{T}"/>
        /// after <see cref="Transaction{T}.Actions"/> are evaluated.
        /// </summary>
        /// <seealso cref="PreEvaluationHash"/>
        /// <seealso cref="StateRootHash"/>
        public BlockHash Hash
        {
            get
            {
                return _hash
                    ?? throw new InvalidOperationException("Hash is not set.");
            }
        }

        /// <summary>
        /// The hash derived from the block <em>except of</em>
        /// <see cref="StateRootHash"/> (i.e., without action evaluation).
        /// Used for <see cref="BlockHeader.Validate"/> checking <see cref="Nonce"/>.
        /// </summary>
        /// <seealso cref="Nonce"/>
        /// <seealso cref="BlockHeader.Validate"/>
        public BlockHash PreEvaluationHash
        {
            get
            {
                return _preEvaluationHash
                    ?? throw new InvalidOperationException("PreEvaluationHash is not set.");
            }
        }

        /// <summary>
        /// The <see cref="ITrie.Hash"/> of the states on the block.
        /// </summary>
        /// <seealso cref="ITrie.Hash"/>
        public HashDigest<SHA256>? StateRootHash { get; }

        [IgnoreDuringEquals]
        public long Index { get; }

        [IgnoreDuringEquals]
        public long Difficulty { get; }

        [IgnoreDuringEquals]
        public BigInteger TotalDifficulty { get; }

        [IgnoreDuringEquals]
        public Nonce Nonce { get; }

        [IgnoreDuringEquals]
        public Address? Miner { get; }

        /// <summary>
        /// The <see cref="Hash"/> of its previous block.
        /// This field is mandatory except for a genesis block.
        /// </summary>
        [IgnoreDuringEquals]
        public BlockHash? PreviousHash { get; }

        [IgnoreDuringEquals]
        public DateTimeOffset Timestamp { get; }

        [IgnoreDuringEquals]
        public HashDigest<SHA256>? TxHash { get; }

        [IgnoreDuringEquals]
        public IReadOnlyList<Transaction<T>> Transactions { get; }

        /// <summary>
        /// The bytes length in its serialized format.
        /// </summary>
        [IgnoreDuringEquals]
        public int BytesLength
        {
            get
            {
                return _bytesLength ?? (int)(_bytesLength = Serialize().Length);
            }
        }

        /// <summary>
        /// The <see cref="BlockHeader"/> of the block.
        /// </summary>
        [IgnoreDuringEquals]
        public BlockHeader Header
        {
            // FIXME: Even though old implicit logic in the constructor is made slightly more
            // explicit, this is still hard to understand and problematic.  Should be
            // refactored further.
            // See also <https://github.com/planetarium/libplanet/issues/1164>.
            get
            {
#pragma warning disable SA1118
                // FIXME: When hash is not assigned, should throw an exception.
                return _header
                    ?? (_preEvaluationHash is null
                        ? (BlockHeader)(_header = new BlockHeader(
                            protocolVersion: ProtocolVersion,
                            index: Index,
                            timestamp: Timestamp.ToString(
                                BlockHeader.TimestampFormat,
                                CultureInfo.InvariantCulture),
                            nonce: Nonce.ToByteArray().ToImmutableArray(),
                            miner: Miner?.ToByteArray().ToImmutableArray()
                                ?? ImmutableArray<byte>.Empty,
                            difficulty: Difficulty,
                            totalDifficulty: TotalDifficulty,
                            previousHash: PreviousHash?.ToByteArray().ToImmutableArray()
                                ?? ImmutableArray<byte>.Empty,
                            txHash: TxHash?.ToByteArray().ToImmutableArray()
                                ?? ImmutableArray<byte>.Empty))
                        : (BlockHeader)(_header = new BlockHeader(
                            protocolVersion: ProtocolVersion,
                            index: Index,
                            timestamp: Timestamp.ToString(
                                BlockHeader.TimestampFormat,
                                CultureInfo.InvariantCulture),
                            nonce: Nonce.ToByteArray().ToImmutableArray(),
                            miner: Miner?.ToByteArray().ToImmutableArray()
                                ?? ImmutableArray<byte>.Empty,
                            difficulty: Difficulty,
                            totalDifficulty: TotalDifficulty,
                            previousHash: PreviousHash?.ToByteArray().ToImmutableArray()
                                ?? ImmutableArray<byte>.Empty,
                            txHash: TxHash?.ToByteArray().ToImmutableArray()
                                ?? ImmutableArray<byte>.Empty,
                            preEvaluationHash: PreEvaluationHash.ToByteArray().ToImmutableArray(),
                            stateRootHash: StateRootHash?.ToByteArray().ToImmutableArray()
                                ?? ImmutableArray<byte>.Empty)));
#pragma warning restore SA1118
            }
        }

        public static bool operator ==(Block<T> left, Block<T> right) =>
            Operator.Weave(left, right);

        public static bool operator !=(Block<T> left, Block<T> right) =>
            Operator.Weave(left, right);

        /// <summary>
        /// Generate a block with given <paramref name="transactions"/>.
        /// </summary>
        /// <param name="index">Index of the block.</param>
        /// <param name="difficulty">Difficulty to find the <see cref="Block{T}"/>
        /// <see cref="Nonce"/>.</param>
        /// <param name="previousTotalDifficulty">The total difficulty until the previous
        /// <see cref="Block{T}"/>.</param>
        /// <param name="miner">The <see cref="Address"/> of miner that mined the block.</param>
        /// <param name="previousHash">
        /// The <see cref="HashDigest{SHA256}"/> of previous block.
        /// </param>
        /// <param name="timestamp">The <see cref="DateTimeOffset"/> when mining started.</param>
        /// <param name="transactions"><see cref="Transaction{T}"/>s that are going to be included
        /// in the block.</param>
        /// <param name="protocolVersion">The protocol version.</param>
        /// <param name="cancellationToken">
        /// A cancellation token used to propagate notification that this
        /// operation should be canceled.</param>
        /// <returns>A <see cref="Block{T}"/> that mined.</returns>
        public static Block<T> Mine(
            long index,
            long difficulty,
            BigInteger previousTotalDifficulty,
            Address miner,
            BlockHash? previousHash,
            DateTimeOffset timestamp,
            IEnumerable<Transaction<T>> transactions,
            int protocolVersion = CurrentProtocolVersion,
            CancellationToken cancellationToken = default(CancellationToken))
        {
            var txs = transactions.OrderBy(tx => tx.Id).ToImmutableArray();
            Block<T> MakeBlock(Nonce n) => new Block<T>(
                index,
                difficulty,
                previousTotalDifficulty + difficulty,
                n,
                miner,
                previousHash,
                timestamp,
                txs,
                protocolVersion: protocolVersion);

            // Poor man' way to optimize stamp...
            // FIXME: We need to rather reorganize the serialization layout.
            byte[] emptyNonce = MakeBlock(new Nonce(new byte[0])).Header.SerializeForHash();
            byte[] oneByteNonce = MakeBlock(new Nonce(new byte[1])).Header.SerializeForHash();
            int offset = 0;
            while (offset < emptyNonce.Length && emptyNonce[offset].Equals(oneByteNonce[offset]))
            {
                offset++;
            }

            const int nonceLength = 2;  // In Bencodex, empty bytes are represented as "0:".
            byte[] stampPrefix = new byte[offset];
            Array.Copy(emptyNonce, stampPrefix, stampPrefix.Length);
            byte[] stampSuffix = new byte[emptyNonce.Length - offset - nonceLength];
            Array.Copy(emptyNonce, offset + nonceLength, stampSuffix, 0, stampSuffix.Length);

            Nonce nonce = Hashcash.Answer(
                n =>
                {
                    int nLen = n.ByteArray.Length;
                    byte[] nLenStr = Encoding.ASCII.GetBytes(
                        nLen.ToString(CultureInfo.InvariantCulture));
                    int totalLen =
                        stampPrefix.Length + nLenStr.Length + 1 + nLen + stampSuffix.Length;
                    byte[] stamp = new byte[totalLen];
                    Array.Copy(stampPrefix, stamp, stampPrefix.Length);
                    int pos = stampPrefix.Length;
                    Array.Copy(nLenStr, 0, stamp, pos, nLenStr.Length);
                    pos += nLenStr.Length;
                    stamp[pos] = 0x3a;  // ':'
                    pos++;
                    n.ByteArray.CopyTo(stamp, pos);
                    pos += nLen;
                    Array.Copy(stampSuffix, 0, stamp, pos, stampSuffix.Length);
                    return stamp;
                },
                difficulty,
                cancellationToken
            );

            return MakeBlock(nonce);
        }

        /// <summary>
        /// Decodes a <see cref="Block{T}"/>'s
        /// <a href="https://bencodex.org/">Bencodex</a> representation.
        /// </summary>
        /// <param name="bytes">A <a href="https://bencodex.org/">Bencodex</a>
        /// representation of a <see cref="Block{T}"/>.</param>
        /// <returns>A decoded <see cref="Block{T}"/> object.</returns>
        /// <seealso cref="Serialize()"/>
        [Pure]
        public static Block<T> Deserialize(byte[] bytes)
        {
            IValue value = new Codec().Decode(bytes);
            if (!(value is Bencodex.Types.Dictionary dict))
            {
                throw new DecodingException(
                    $"Expected {typeof(Bencodex.Types.Dictionary)} but " +
                    $"{value.GetType()}");
            }

            var block = new Block<T>(dict);
            block._bytesLength = bytes.Length;
            return block;
        }

        public byte[] Serialize()
        {
            var codec = new Codec();
            byte[] serialized = codec.Encode(ToBencodex());
            return serialized;
        }

        public Bencodex.Types.Dictionary ToBencodex() => ToRawBlock().ToBencodex();

        /// <summary>
        /// Gets <see cref="BlockDigest"/> representation of the <see cref="Block{T}"/>.
        /// </summary>
        /// <returns><see cref="BlockDigest"/> representation of the <see cref="Block{T}"/>.
        /// </returns>
        public BlockDigest ToBlockDigest()
        {
            return new BlockDigest(
                header: Header,
                txIds: Transactions
                    .Select(tx => tx.Id.ToByteArray().ToImmutableArray())
                    .ToImmutableArray());
        }

        public override string ToString()
        {
            return Hash.ToString();
        }

        /// <summary>
        /// Validates this <see cref="Block{T}"/> and throws an appropriate exception
        /// if not valid.
        /// </summary>
        /// <param name="currentTime">The current time to validate time-wise conditions.</param>
        /// <exception cref="InvalidBlockHashException">Thrown when <see cref="Hash"/>
        /// is invalid.</exception>
        /// <exception cref="InvalidBlockTimestampException">Thrown when <see cref="Timestamp"/>
        /// is invalid.  For example, if <see cref="Timestamp"/> is too far in the future
        /// compared to <paramref name="currentTime"/>.</exception>
        /// <exception cref="InvalidBlockIndexException">Thrown when <see cref="Index"/>
        /// is invalid.  For example, if it is a negative integer.
        /// </exception>
        /// <exception cref="InvalidBlockDifficultyException">Thrown when <see cref="Difficulty"/>
        /// is not properly configured.  For example, if it is too easy.</exception>
        /// <exception cref="InvalidBlockPreviousHashException">Thrown when
        /// <see cref="PreviousHash"/> is invalid so that the <see cref="Block{T}"/>s are not
        /// continuous.</exception>
        /// <exception cref="InvalidBlockNonceException">Thrown when
        /// <see cref="Nonce"/> does not satisfy the <see cref="Difficulty"/> level.</exception>
        /// <exception cref="InvalidBlockTxHashException">Thrown when the value of
        /// <see cref="TxHash"/> is not consistent with <see cref="Transactions"/>.
        /// </exception>
        internal void Validate(DateTimeOffset currentTime)
        {
            Header.Validate(currentTime);

            foreach (Transaction<T> tx in Transactions)
            {
                tx.Validate();
            }

            HashDigest<SHA256>? calculatedTxHash =
                CalculateTxHashes(Transactions.OrderBy(tx => tx.Id));
            if (!calculatedTxHash.Equals(TxHash))
            {
                throw new InvalidBlockTxHashException(
                    $"Block #{Index} {Hash}'s TxHash doesn't match its content.",
                    TxHash,
                    calculatedTxHash
                );
            }
        }

        internal RawBlock ToRawBlock()
        {
            return new RawBlock(
                header: Header,
                transactions: Transactions
                .Select(tx => tx.Serialize(true).ToImmutableArray()).ToImmutableArray());
        }

        private static HashDigest<SHA256>? CalculateTxHashes(IEnumerable<Transaction<T>> txs)
        {
            if (!txs.Any())
            {
                return null;
            }

            byte[][] serializedTxs = txs.Select(tx => tx.Serialize(true)).ToArray();
            int txHashSourceLength = serializedTxs.Select(b => b.Length).Sum() + 2;
            var txHashSource = new byte[txHashSourceLength];

            // Bencodex lists look like: l...e
            txHashSource[0] = 0x6c;
            txHashSource[txHashSourceLength - 1] = 0x65;
            int offset = 1;
            foreach (byte[] serializedTx in serializedTxs)
            {
                serializedTx.CopyTo(txHashSource, offset);
                offset += serializedTx.Length;
            }

            using SHA256 hashAlgo = SHA256.Create();
            return HashDigest<SHA256>.DeriveFrom(txHashSource);
        }

        private readonly struct BlockSerializationContext
        {
            public BlockSerializationContext(bool hash, bool transactionData)
            {
                IncludeHash = hash;
                IncludeTransactionData = transactionData;
            }

            internal bool IncludeHash { get; }

            internal bool IncludeTransactionData { get; }
        }
    }
}
