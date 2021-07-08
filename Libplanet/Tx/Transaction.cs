using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Globalization;
using System.Linq;
using System.Security.Cryptography;
using Bencodex;
using Bencodex.Types;
using Libplanet.Action;
using Libplanet.Assets;
using Libplanet.Blocks;
using Libplanet.Crypto;
using Libplanet.Store.Trie;

namespace Libplanet.Tx
{
    /// <summary>
    /// Consists of <see cref="IAction"/> and is signed to be included in
    /// a <see cref="Blocks.Block{T}"/> and transmitted over the network.
    /// </summary>
    /// <typeparam name="T">A class implementing <see cref="IAction"/> to
    /// include.
    /// Each game usually defines its own concrete class which implements
    /// <see cref="IAction"/>, and uses it for this type parameter.
    /// This type parameter is aligned with <see cref="Blocks.Block{T}"/>'s
    /// and <see cref="Blockchain.BlockChain{T}"/>'s type parameters.
    /// </typeparam>
    /// <seealso cref="IAction"/>
    /// <seealso cref="PolymorphicAction{T}"/>
    public sealed class Transaction<T> : IEquatable<Transaction<T>>
        where T : IAction, new()
    {
        private const string TimestampFormat = "yyyy-MM-ddTHH:mm:ss.ffffffZ";

        // If a tx is longer than 50 KiB don't cache its bytes representation to _bytes.
        private const int BytesCacheThreshold = 50 * 1024;

        private TxId? _id;
        private byte[] _signature;
        private byte[] _bytes;
        private int _bytesLength;

        /// <summary>
        /// Creates a new <see cref="Transaction{T}"/>.
        /// <para>This constructor takes all required and only required values
        /// for a <see cref="Transaction{T}"/>, so gives you full control of
        /// creating a <see cref="Transaction{T}"/>, and in other words,
        /// this constructor is only useful when all details of
        /// a <see cref="Transaction{T}"/> need to be manually adjusted.
        /// For the most cases, the fa&#xe7;ade factory <see
        /// cref="Create(long, PrivateKey, BlockHash?, IEnumerable{T},
        /// IImmutableSet{Address}, DateTimeOffset?)"/> is more useful.</para>
        /// </summary>
        /// <param name="nonce">The number of previous
        /// <see cref="Transaction{T}"/>s committed by the <see cref="Signer"/>
        /// of this transaction.  This goes to the
        /// <see cref="Transaction{T}.Nonce"/> property.</param>
        /// <param name="signer">An <see cref="Address"/> of the account
        /// who signs this transaction.  If this is not derived from <paramref
        /// name="publicKey"/> <see cref="InvalidTxPublicKeyException"/> is
        /// thrown.  This goes to the <see cref="Signer"/> property.</param>
        /// <param name="publicKey">A <see cref="PublicKey"/> of the account
        /// who signs this transaction.  If this does not match to <paramref
        /// name="signer"/> address <see cref="InvalidTxPublicKeyException"/>
        /// is thrown.  This cannot be <c>null</c>.  This goes to
        /// the <see cref="PublicKey"/> property.</param>
        /// <param name="genesisHash">A <see cref="HashDigest{SHA256}"/> value
        /// of the genesis which this <see cref="Transaction{T}"/> is made from.
        /// This can be <c>null</c> iff the transaction is contained
        /// in the genesis block.
        /// </param>
        /// <param name="updatedAddresses"><see cref="Address"/>es whose
        /// states affected by <paramref name="actions"/>.  This goes to
        /// the <see cref="UpdatedAddresses"/> property.</param>
        /// <param name="timestamp">The time this <see cref="Transaction{T}"/>
        /// is created and signed.  This goes to the <see cref="Timestamp"/>
        /// property.</param>
        /// <param name="actions">A list of <see cref="IAction"/>s.  This
        /// can be empty, but cannot be <c>null</c>.  This goes to
        /// the <see cref="Actions"/> property.</param>
        /// <param name="signature">A digital signature of the content of
        /// this <see cref="Transaction{T}"/>.  This has to be signed by
        /// the account who corresponds to <paramref name="publicKey"/>,
        /// or it will throw <see cref="InvalidTxSignatureException"/>.
        /// This is copied and then assigned to the <see cref="Signature"/>
        /// property.</param>
        /// <exception cref="ArgumentNullException">Thrown when <c>null</c>
        /// is passed to <paramref name="signature"/>,
        /// <paramref name="actions"/>, or <paramref name="publicKey"/>.
        /// </exception>
        public Transaction(
            long nonce,
            Address signer,
            PublicKey publicKey,
            BlockHash? genesisHash,
            IImmutableSet<Address> updatedAddresses,
            DateTimeOffset timestamp,
            IEnumerable<T> actions,
            byte[] signature)
        {
            Nonce = nonce;
            Signer = signer;
            GenesisHash = genesisHash;
            UpdatedAddresses = updatedAddresses ??
                               throw new ArgumentNullException(nameof(updatedAddresses));
            Signature = signature ??
                        throw new ArgumentNullException(nameof(signature));
            Timestamp = timestamp;
            Actions = actions?.ToImmutableList() ??
                      throw new ArgumentNullException(nameof(actions));
            PublicKey = publicKey ??
                        throw new ArgumentNullException(nameof(publicKey));
        }

        /// <summary>
        /// Creates a <see cref="Transaction{T}"/> instance from its serialization.
        /// </summary>
        /// <param name="dict">The <see cref="Bencodex.Types.Dictionary"/>
        /// representation of <see cref="Transaction{T}"/> instance.
        /// </param>
        public Transaction(Bencodex.Types.Dictionary dict)
            : this(new RawTransaction(dict))
        {
        }

#pragma warning disable SA1118 // Parameter spans multiple line
        internal Transaction(RawTransaction rawTx)
            : this(
                rawTx.Nonce,
                new Address(rawTx.Signer),
                new PublicKey(rawTx.PublicKey.ToArray()),
                rawTx.GenesisHash != ImmutableArray<byte>.Empty
                    ? new BlockHash(rawTx.GenesisHash.ToArray())
                    : (BlockHash?)null,
                rawTx.UpdatedAddresses.Select(
                    a => new Address(a)
                ).ToImmutableHashSet(),
                DateTimeOffset.ParseExact(
                    rawTx.Timestamp,
                    TimestampFormat,
                    CultureInfo.InvariantCulture).ToUniversalTime(),
                rawTx.Actions.Select(ToAction).ToImmutableList(),
                rawTx.Signature.ToArray())
#pragma warning restore SA1118 // Parameter spans multiple line
        {
        }

        private Transaction(
            long nonce,
            Address signer,
            PublicKey publicKey,
            BlockHash? genesisHash,
            IImmutableSet<Address> updatedAddresses,
            DateTimeOffset timestamp,
            IEnumerable<T> actions)
            : this(
                nonce,
                signer,
                publicKey,
                genesisHash,
                updatedAddresses,
                timestamp,
                actions.ToImmutableList(),
                new byte[0])
        {
        }

        /// <summary>
        /// A unique identifier derived from this <see cref="Transaction{T}"/>'s
        /// content.
        /// <para>For more characteristics, see <see cref="TxId"/> type.</para>
        /// </summary>
        /// <seealso cref="TxId"/>
        public TxId Id
        {
            get
            {
                if (!(_id is { } nonNull))
                {
                    using var hasher = SHA256.Create();
                    byte[] payload = Serialize(true);
                    _id = nonNull = new TxId(hasher.ComputeHash(payload));
                }

                return nonNull;
            }
        }

        /// <summary>
        /// The number of previous <see cref="Transaction{T}"/>s committed by
        /// the <see cref="Signer"/> of this transaction.
        /// </summary>
        public long Nonce { get; }

        /// <summary>
        /// A <see cref="PublicKey"/> of the account who signs this transaction.
        /// This is derived from the <see cref="PublicKey"/>.
        /// </summary>
        public Address Signer { get; }

        /// <summary>
        /// <see cref="Address"/>es whose states affected by
        /// <see cref="Actions"/>.
        /// </summary>
        public IImmutableSet<Address> UpdatedAddresses { get; }

        /// <summary>
        /// A digital signature of the content of this
        /// <see cref="Transaction{T}"/>.  This is signed by the account
        /// who corresponds to <see cref="PublicKey"/>.
        /// This cannot be <c>null</c>.
        /// </summary>
        /// <returns>A new <see cref="byte"/> array of this transaction's
        /// signature.  Changing a returned array does not affect the internal
        /// state of this <see cref="Transaction{T}"/> object.</returns>
        public byte[] Signature
        {
            get
            {
                var sig = new byte[_signature.Length];
                Array.Copy(_signature, sig, _signature.Length);
                return sig;
            }

            private set
            {
                _signature = new byte[value.Length];
                Array.Copy(value, _signature, value.Length);
            }
        }

        /// <summary>
        /// A list of <see cref="IAction"/>s.  These are executed in the order.
        /// This can be empty, but cannot be <c>null</c>.
        /// </summary>
        public IImmutableList<T> Actions { get; }

        /// <summary>
        /// The time this <see cref="Transaction{T}"/> is created and signed.
        /// </summary>
        public DateTimeOffset Timestamp { get; }

        /// <summary>
        /// A <see cref="PublicKey"/> of the account who signs this
        /// <see cref="Transaction{T}"/>.
        /// The <see cref="Signer"/> address is always corresponding to this
        /// for each transaction.  This cannot be <c>null</c>.
        /// </summary>
        public PublicKey PublicKey { get; }

        /// <summary>
        /// A <see cref="HashDigest{SHA256}"/> value of the genesis which this
        /// <see cref="Transaction{T}"/> is made from.
        /// This can be <c>null</c> iff the transaction is contained
        /// in the genesis block.
        /// </summary>
        public BlockHash? GenesisHash { get; }

        /// <summary>
        /// The bytes length in its serialized format.
        /// </summary>
        public int BytesLength
        {
            get
            {
                // Note that Serialize() by itself caches _byteLength, so that this ByteLength
                // property never invokes Serialize() more than once.
                return _bytesLength > 0 ? _bytesLength : Serialize(true).Length;
            }
        }

        /// <summary>
        /// Decodes a <see cref="Transaction{T}"/>'s
        /// <a href="https://bencodex.org/">Bencodex</a> representation.
        /// </summary>
        /// <param name="bytes">A <a href="https://bencodex.org/">Bencodex</a>
        /// representation of a <see cref="Transaction{T}"/>.</param>
        /// <param name="validate">Whether to validate the transaction.</param>
        /// <returns>A decoded <see cref="Transaction{T}"/> object.</returns>
        /// <exception cref="InvalidTxSignatureException">Thrown when its
        /// <see cref="Signature"/> is invalid or not signed by
        /// the account who corresponds to <see cref="PublicKey"/>.
        /// </exception>
        /// <exception cref="InvalidTxPublicKeyException">Thrown when its
        /// <see cref="Signer"/> is not derived from its
        /// <see cref="PublicKey"/>.</exception>
        /// <seealso cref="Serialize(bool)"/>
        public static Transaction<T> Deserialize(byte[] bytes, bool validate = true)
        {
            IValue value = new Codec().Decode(bytes);
            if (!(value is Bencodex.Types.Dictionary dict))
            {
                throw new DecodingException(
                    $"Expected {typeof(Bencodex.Types.Dictionary)} but " +
                    $"{value.GetType()}");
            }

            var tx = new Transaction<T>(dict);
            if (validate)
            {
                tx.Validate();
            }

            if (bytes.Length < BytesCacheThreshold)
            {
                tx._bytes = bytes;
            }

            tx._bytesLength = bytes.Length;
            return tx;
        }

        /// <summary>
        /// A fa&#xe7;ade factory to create a new <see cref="Transaction{T}"/>.
        /// Unlike the <see cref="Transaction(long, Address, PublicKey, BlockHash?,
        /// IImmutableSet{Address}, DateTimeOffset, IEnumerable{T}, byte[])"/>
        /// constructor, it automatically fills the following values from:
        /// <list type="table">
        /// <listheader>
        /// <term>Property</term>
        /// <description>Parameter the filled value derived from</description>
        /// </listheader>
        /// <item>
        /// <term><see cref="Signer"/></term>
        /// <description><paramref name="privateKey"/></description>
        /// </item>
        /// <item>
        /// <term><see cref="PublicKey"/></term>
        /// <description><paramref name="privateKey"/></description>
        /// </item>
        /// <item>
        /// <term><see cref="UpdatedAddresses"/></term>
        /// <description><paramref name="actions"/> and
        /// <paramref name="updatedAddresses"/></description>
        /// </item>
        /// </list>
        /// <para>Note that the <paramref name="privateKey"/> in itself is not
        /// included in the created <see cref="Transaction{T}"/>.</para>
        /// </summary>
        /// <remarks>
        /// This factory method tries its best to fill the <see
        /// cref="UpdatedAddresses"/> property by actually evaluating
        /// the given <paramref name="actions"/> (we call it &#x201c;rehearsal
        /// mode&#x201d;), but remember that its result
        /// is approximated in some degree, because the result of
        /// <paramref name="actions"/> are not deterministic until
        /// the <see cref="Transaction{T}"/> belongs to a <see
        /// cref="Libplanet.Blocks.Block{T}"/>.
        /// <para>If an <see cref="IAction"/> depends on previous states or
        /// some randomness to determine what <see cref="Address"/> to update,
        /// the automatically filled <see cref="UpdatedAddresses"/> became
        /// mismatched from the <see cref="Address"/>es
        /// <paramref name="actions"/> actually update after
        /// a <see cref="Libplanet.Blocks.Block{T}"/> is mined.
        /// Although such case would be rare, a programmer could manually give
        /// the <paramref name="updatedAddresses"/> parameter
        /// the <see cref="Address"/>es they predict to be updated.</para>
        /// <para>If an <see cref="IAction"/> oversimplifies the assumption
        /// about the <see cref="Libplanet.Blocks.Block{T}"/> it belongs to,
        /// runtime exceptions could be thrown from this factory method.
        /// The best solution to that is not to oversimplify things,
        /// there is an option to check <see cref="IActionContext"/>'s
        /// <see cref="IActionContext.Rehearsal"/> is <c>true</c> and
        /// a conditional logic for the case.</para>
        /// </remarks>
        /// <param name="nonce">The number of previous
        /// <see cref="Transaction{T}"/>s committed by the <see cref="Signer"/>
        /// of this transaction.  This goes to the
        /// <see cref="Transaction{T}.Nonce"/> property.</param>
        /// <param name="privateKey">A <see cref="PrivateKey"/> of the account
        /// who creates and signs a new transaction.  This key is used to fill
        /// the <see cref="Signer"/>, <see cref="PublicKey"/>, and
        /// <see cref="Signature"/> properties, but this in itself is not
        /// included in the transaction.</param>
        /// <param name="genesisHash">A <see cref="HashDigest{SHA256}"/> value
        /// of the genesis which this <see cref="Transaction{T}"/> is made from.
        /// This can be <c>null</c> iff the transaction is contained
        /// in the genesis block.
        /// </param>
        /// <param name="actions">A list of <see cref="IAction"/>s.  This
        /// can be empty, but cannot be <c>null</c>.  This goes to
        /// the <see cref="Actions"/> property, and <see cref="IAction"/>s
        /// are evaluated before a <see cref="Transaction{T}"/> is created
        /// in order to fill the <see cref="UpdatedAddresses"/>.  See also
        /// <em>Remarks</em> section.</param>
        /// <param name="updatedAddresses"><see cref="Address"/>es whose
        /// states affected by <paramref name="actions"/>.
        /// These <see cref="Address"/>es are also included in
        /// the <see cref="UpdatedAddresses"/> property, besides
        /// <see cref="Address"/>es projected by evaluating
        /// <paramref name="actions"/>.  See also <em>Remarks</em> section.
        /// </param>
        /// <param name="timestamp">The time this <see cref="Transaction{T}"/>
        /// is created and signed.  This goes to the <see cref="Timestamp"/>
        /// property.  If <c>null</c> (which is default) is passed this will
        /// be the current time.</param>
        /// <returns>A created new <see cref="Transaction{T}"/> signed by
        /// the given <paramref name="privateKey"/>.</returns>
        /// <exception cref="ArgumentNullException">Thrown when <c>null</c>
        /// is passed to <paramref name="privateKey"/> or
        /// or <paramref name="actions"/>.
        /// </exception>
        public static Transaction<T> Create(
            long nonce,
            PrivateKey privateKey,
            BlockHash? genesisHash,
            IEnumerable<T> actions,
            IImmutableSet<Address> updatedAddresses = null,
            DateTimeOffset? timestamp = null
        )
        {
            if (ReferenceEquals(privateKey, null))
            {
                throw new ArgumentNullException(nameof(privateKey));
            }

            Transaction<T> unsignedTransaction = CreateUnsigned(
                nonce,
                privateKey.PublicKey,
                genesisHash,
                actions,
                updatedAddresses,
                timestamp);
            byte[] payload = unsignedTransaction.Serialize(false);
            byte[] sig = privateKey.Sign(payload);
            return new Transaction<T>(
                unsignedTransaction.Nonce,
                unsignedTransaction.Signer,
                unsignedTransaction.PublicKey,
                unsignedTransaction.GenesisHash,
                unsignedTransaction.UpdatedAddresses,
                unsignedTransaction.Timestamp,
                unsignedTransaction.Actions,
                sig);
        }

        /// <summary>
        /// A fa&#xe7;ade factory to create a new <see cref="Transaction{T}"/>.
        /// Unlike the <see cref="Transaction(long, Address, PublicKey, BlockHash?,
        /// IImmutableSet{Address}, DateTimeOffset, IEnumerable{T}, byte[])"/>
        /// constructor, it automatically fills the following values from:
        /// <list type="table">
        /// <listheader>
        /// <term>Property</term>
        /// <description>Parameter the filled value derived from</description>
        /// </listheader>
        /// <item>
        /// <term><see cref="Signer"/></term>
        /// <description><paramref name="publicKey"/></description>
        /// </item>
        /// <item>
        /// <term><see cref="PublicKey"/></term>
        /// <description><paramref name="publicKey"/></description>
        /// </item>
        /// <item>
        /// <term><see cref="UpdatedAddresses"/></term>
        /// <description><paramref name="actions"/> and
        /// <paramref name="updatedAddresses"/></description>
        /// </item>
        /// </list>
        /// </summary>
        /// <remarks>
        /// This factory method tries its best to fill the <see
        /// cref="UpdatedAddresses"/> property by actually evaluating
        /// the given <paramref name="actions"/> (we call it &#x201c;rehearsal
        /// mode&#x201d;), but remember that its result
        /// is approximated in some degree, because the result of
        /// <paramref name="actions"/> are not deterministic until
        /// the <see cref="Transaction{T}"/> belongs to a <see
        /// cref="Libplanet.Blocks.Block{T}"/>.
        /// <para>If an <see cref="IAction"/> depends on previous states or
        /// some randomness to determine what <see cref="Address"/> to update,
        /// the automatically filled <see cref="UpdatedAddresses"/> became
        /// mismatched from the <see cref="Address"/>es
        /// <paramref name="actions"/> actually update after
        /// a <see cref="Libplanet.Blocks.Block{T}"/> is mined.
        /// Although such case would be rare, a programmer could manually give
        /// the <paramref name="updatedAddresses"/> parameter
        /// the <see cref="Address"/>es they predict to be updated.</para>
        /// <para>If an <see cref="IAction"/> oversimplifies the assumption
        /// about the <see cref="Libplanet.Blocks.Block{T}"/> it belongs to,
        /// runtime exceptions could be thrown from this factory method.
        /// The best solution to that is not to oversimplify things,
        /// there is an option to check <see cref="IActionContext"/>'s
        /// <see cref="IActionContext.Rehearsal"/> is <c>true</c> and
        /// a conditional logic for the case.</para>
        /// </remarks>
        /// <param name="nonce">The number of previous
        /// <see cref="Transaction{T}"/>s committed by the <see cref="Signer"/>
        /// of this transaction.  This goes to the
        /// <see cref="Transaction{T}.Nonce"/> property.</param>
        /// <param name="publicKey">A <see cref="PublicKey"/> of the account
        /// who creates a new transaction.  This key is used to fill
        /// the <see cref="Signer"/> and <see cref="PublicKey"/> properties,
        /// but this in itself is not included in the transaction.</param>
        /// <param name="genesisHash">A <see cref="HashDigest{SHA256}"/> value
        /// of the genesis which this <see cref="Transaction{T}"/> is made from.
        /// This can be <c>null</c> iff the transaction is contained
        /// in the genesis block.
        /// </param>
        /// <param name="actions">A list of <see cref="IAction"/>s.  This
        /// can be empty, but cannot be <c>null</c>.  This goes to
        /// the <see cref="Actions"/> property, and <see cref="IAction"/>s
        /// are evaluated before a <see cref="Transaction{T}"/> is created
        /// in order to fill the <see cref="UpdatedAddresses"/>.  See also
        /// <em>Remarks</em> section.</param>
        /// <param name="updatedAddresses"><see cref="Address"/>es whose
        /// states affected by <paramref name="actions"/>.
        /// These <see cref="Address"/>es are also included in
        /// the <see cref="UpdatedAddresses"/> property, besides
        /// <see cref="Address"/>es projected by evaluating
        /// <paramref name="actions"/>.  See also <em>Remarks</em> section.
        /// </param>
        /// <param name="timestamp">The time this <see cref="Transaction{T}"/>
        /// is created.  This goes to the <see cref="Timestamp"/>
        /// property.  If <c>null</c> (which is default) is passed this will
        /// be the current time.</param>
        /// <returns>A created new <see cref="Transaction{T}"/> unsigned.</returns>
        /// <exception cref="ArgumentNullException">Thrown when <c>null</c>
        /// is passed to <paramref name="actions"/>.
        /// </exception>
        public static Transaction<T> CreateUnsigned(
            long nonce,
            PublicKey publicKey,
            BlockHash? genesisHash,
            IEnumerable<T> actions,
            IImmutableSet<Address> updatedAddresses = null,
            DateTimeOffset? timestamp = null
        )
        {
            var signer = new Address(publicKey);

            if (ReferenceEquals(updatedAddresses, null))
            {
                updatedAddresses = ImmutableHashSet<Address>.Empty;
            }

            DateTimeOffset ts = timestamp ?? DateTimeOffset.UtcNow;

            ImmutableArray<T> actionsArray = actions.ToImmutableArray();
            if (!actionsArray.IsEmpty)
            {
                // FIXME: Although we are assuming all block hashes are SHA256 digest, we should
                // parametrize this in the future.
                BlockHash emptyBlockHash = BlockHash.FromHashDigest(default(HashDigest<SHA256>));

                IAccountStateDelta delta = new Transaction<T>(
                    nonce,
                    signer,
                    publicKey,
                    genesisHash,
                    updatedAddresses,
                    ts,
                    actionsArray
                ).EvaluateActions(
                    emptyBlockHash,
                    0,
                    new AccountStateDeltaImpl(
                        _ => null,
                        (_, c) => new FungibleAssetValue(c),
                        signer
                    ),
                    signer,
                    rehearsal: true
                );
                if (!updatedAddresses.IsSupersetOf(delta.UpdatedAddresses))
                {
                    updatedAddresses =
                        updatedAddresses.Union(delta.UpdatedAddresses);
                }
            }

            return new Transaction<T>(
                nonce,
                signer,
                publicKey,
                genesisHash,
                updatedAddresses,
                ts,
                actionsArray);
        }

        /// <summary>
        /// Encodes this <see cref="Transaction{T}"/> into a <see cref="byte"/> array.
        /// </summary>
        /// <param name="sign">Whether to include its <see cref="Signature"/>.
        /// </param>
        /// <returns>A <a href="https://bencodex.org/">Bencodex</a>
        /// representation of this <see cref="Transaction{T}"/>.</returns>
        public byte[] Serialize(bool sign)
        {
            Codec codec = null;
            if (_bytes is { })
            {
                if (sign)
                {
                    return _bytes;
                }

                // Poor man's way to optimize serialization without signature...
                // FIXME: We need to rather reorganize the serialization layout
                //        & optimize Bencodex.Codec in general.
                if (_signature is { } && _signature.Length > 0)
                {
                    codec = new Codec();
                    byte[] sigDict =
                        codec.Encode(Dictionary.Empty.Add(RawTransaction.SignatureKey, _signature));
                    var sigField = new byte[sigDict.Length - 1];
                    Array.Copy(sigDict, 1, sigField, 0, sigField.Length);
                    int sigOffset = _bytes.IndexOf(sigField);
                    if (sigOffset > 0)
                    {
                        int sigEnd = sigOffset + _signature.Length;
                        var buffer = new byte[_bytes.Length - sigField.Length];
                        Array.Copy(_bytes, buffer, sigOffset);
                        Array.Copy(_bytes, sigEnd, buffer, sigOffset, _bytesLength - sigEnd);
                        return buffer;
                    }
                }
            }

            codec ??= new Codec();
            byte[] serialized = codec.Encode(ToBencodex(sign));
            if (sign)
            {
                if (serialized.Length < BytesCacheThreshold)
                {
                    _bytes = serialized;
                }

                _bytesLength = serialized.Length;
            }

            return serialized;
        }

        /// <summary>
        /// Encodes this <see cref="Transaction{T}"/> into a <see cref="IValue"/>.
        /// </summary>
        /// <param name="sign">Whether to include its <see cref="Signature"/>.
        /// Note that an encoding without signature cannot be decoded.
        /// </param>
        /// <returns>A <see cref="Bencodex.Types.Dictionary"/> typed
        /// <a href="https://bencodex.org/">Bencodex</a>
        /// representation of this <see cref="Transaction{T}"/>.</returns>
        public Bencodex.Types.Dictionary ToBencodex(bool sign) =>
            ToRawTransaction(sign).ToBencodex();

        /// <summary>
        /// Executes the <see cref="Actions"/> step by step, and emits
        /// <see cref="ActionEvaluation"/> for each step.
        /// <para>If the needed value is only the final states,
        /// use <see cref="EvaluateActions"/> method instead.</para>
        /// </summary>
        /// <param name="blockHash">The <see
        /// cref="Libplanet.Blocks.Block{T}.Hash"/> of
        /// <see cref="Libplanet.Blocks.Block{T}"/> that this
        /// <see cref="Transaction{T}"/> will belong to.</param>
        /// <param name="blockIndex">The <see
        /// cref="Libplanet.Blocks.Block{T}.Index"/> of
        /// <see cref="Libplanet.Blocks.Block{T}"/> that this
        /// <see cref="Transaction{T}"/> will belong to.</param>
        /// <param name="previousStates">The states immediately before
        /// <see cref="Actions"/> being executed.  Note that its
        /// <see cref="IAccountStateDelta.UpdatedAddresses"/> are remained
        /// to the returned next states.</param>
        /// <param name="minerAddress">An address of block miner.</param>
        /// <param name="rehearsal">Pass <c>true</c> if it is intended
        /// to be dry-run (i.e., the returned result will be never used).
        /// The default value is <c>false</c>.</param>
        /// <param name="previousBlockStatesTrie">The trie to contain states at previous block.
        /// </param>
        /// <returns>Enumerates <see cref="ActionEvaluation"/>s for each one in
        /// <see cref="Actions"/>.
        /// <para>The order is the same to the <see cref="Actions"/>.</para>
        /// <para>Each <see cref="ActionEvaluation"/> includes its previous
        /// <see cref="ActionEvaluation"/>s' delta besides its own delta.</para>
        /// <para>Note that each <see cref="IActionContext.Random"/> object has a unconsumed state.
        /// </para>
        /// </returns>
        [Pure]
        public IEnumerable<ActionEvaluation> EvaluateActionsGradually(
            BlockHash blockHash,
            long blockIndex,
            IAccountStateDelta previousStates,
            Address minerAddress,
            bool rehearsal = false,
            ITrie previousBlockStatesTrie = null
        )
        {
            return ActionEvaluation.EvaluateActionsGradually(
                blockHash,
                blockIndex,
                Id,
                previousStates,
                minerAddress,
                Signer,
                Signature,
                Actions.Cast<IAction>().ToImmutableList(),
                rehearsal,
                previousBlockStatesTrie);
       }

        /// <summary>
        /// Executes the <see cref="Actions"/> and gets the result states.
        /// </summary>
        /// <param name="blockHash">The <see
        /// cref="Libplanet.Blocks.Block{T}.Hash"/> of
        /// <see cref="Libplanet.Blocks.Block{T}"/> that this
        /// <see cref="Transaction{T}"/> will belong to.</param>
        /// <param name="blockIndex">The <see
        /// cref="Libplanet.Blocks.Block{T}.Index"/> of
        /// <see cref="Libplanet.Blocks.Block{T}"/> that this
        /// <see cref="Transaction{T}"/> will belong to.</param>
        /// <param name="previousStates">The states immediately before
        /// <see cref="Actions"/> being executed.  Note that its
        /// <see cref="IAccountStateDelta.UpdatedAddresses"/> are remained
        /// to the returned next states.</param>
        /// <param name="minerAddress">An address of block miner.</param>
        /// <param name="rehearsal">Pass <c>true</c> if it is intended
        /// to be dry-run (i.e., the returned result will be never used).
        /// The default value is <c>false</c>.</param>
        /// <returns>The states immediately after <see cref="Actions"/>
        /// being executed.  Note that it maintains
        /// <see cref="IAccountStateDelta.UpdatedAddresses"/> of the given
        /// <paramref name="previousStates"/> as well.</returns>
        [Pure]
        public IAccountStateDelta EvaluateActions(
            BlockHash blockHash,
            long blockIndex,
            IAccountStateDelta previousStates,
            Address minerAddress,
            bool rehearsal = false
        )
        {
            var evaluations = EvaluateActionsGradually(
                blockHash,
                blockIndex,
                previousStates,
                minerAddress,
                rehearsal: rehearsal
            );

            ActionEvaluation lastEvaluation;
            try
            {
                lastEvaluation = evaluations.Last();
            }
            catch (InvalidOperationException)
            {
                // If "evaluations" is empty:
                return previousStates;
            }

            return lastEvaluation.OutputStates;
        }

        /// <summary>
        /// Validates this <see cref="Transaction{T}"/>.  If there is something
        /// invalid it throws an exception.  If valid it does nothing.
        /// </summary>
        /// <exception cref="InvalidTxSignatureException">Thrown when its
        /// <see cref="Transaction{T}.Signature"/> is invalid or not signed by
        /// the account who corresponds to its <see cref="PublicKey"/>.
        /// </exception>
        /// <exception cref="InvalidTxPublicKeyException">Thrown when its
        /// <see cref="Signer"/> is not derived from its
        /// <see cref="Transaction{T}.PublicKey"/>.</exception>
        public void Validate()
        {
            if (Signature.Length == 0 || !PublicKey.Verify(Serialize(false), Signature))
            {
                string message =
                    $"The signature ({ByteUtil.Hex(Signature)}) is failed " +
                    "to verify.";
                throw new InvalidTxSignatureException(Id, message);
            }

            if (!new Address(PublicKey).Equals(Signer))
            {
                string message =
                    $"The public key ({ByteUtil.Hex(PublicKey.Format(true))} " +
                    $"is not matched to the address ({Signer}).";
                throw new InvalidTxPublicKeyException(Id, message);
            }
        }

        /// <inheritdoc />
        public bool Equals(Transaction<T> other)
        {
            return Id.Equals(other.Id);
        }

        /// <inheritdoc />
        public override bool Equals(object obj)
        {
            if (ReferenceEquals(null, obj))
            {
                return false;
            }

            return obj is Transaction<T> other && Equals(other);
        }

        /// <inheritdoc />
        public override int GetHashCode()
        {
            return Id.GetHashCode();
        }

        internal RawTransaction ToRawTransaction(bool includeSign)
        {
            ImmutableArray<byte> genesisHash =
                GenesisHash?.ToByteArray().ToImmutableArray() ?? ImmutableArray<byte>.Empty;
            var rawTx = new RawTransaction(
                nonce: Nonce,
                signer: Signer.ByteArray,
                genesisHash: genesisHash,
                updatedAddresses: UpdatedAddresses.Select(a =>
                    a.ByteArray).ToImmutableArray(),
                publicKey: PublicKey.Format(false).ToImmutableArray(),
                timestamp: Timestamp.ToString(TimestampFormat, CultureInfo.InvariantCulture),
                actions: Actions.Select(a => a.PlainValue).ToImmutableArray()
            );

            if (includeSign)
            {
                rawTx = rawTx.AddSignature(Signature);
            }

            return rawTx;
        }

        private static T ToAction(IValue value)
        {
            var action = new T();
            action.LoadPlainValue(value);
            return action;
        }

        private readonly struct TransactionSerializationContext
        {
            internal TransactionSerializationContext(bool includeSignature)
            {
                IncludeSignature = includeSignature;
            }

            internal bool IncludeSignature { get; }
        }
    }
}
