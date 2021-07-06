using System;
using System.Collections.Immutable;
using System.Globalization;
using System.Linq;
using System.Numerics;
using Bencodex.Types;
using Libplanet.Blocks;
using Libplanet.Tests.Common.Action;
using Xunit;

namespace Libplanet.Tests.Blocks
{
    public class BlockHeaderTest : IClassFixture<BlockFixture>
    {
        private BlockFixture _fx;

        public BlockHeaderTest(BlockFixture fixture) => _fx = fixture;

        [Fact]
        public void ToBencodex()
        {
            var header = new BlockHeader(
                protocolVersion: 0,
                index: 0,
                difficulty: _fx.Genesis.Difficulty,
                totalDifficulty: _fx.Genesis.TotalDifficulty,
                nonce: _fx.Genesis.Nonce.ByteArray,
                miner: _fx.Genesis.Miner?.ByteArray ?? ImmutableArray<byte>.Empty,
                hash: _fx.Genesis.Hash.ByteArray,
                txHash: _fx.Genesis.TxHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                previousHash: _fx.Genesis.PreviousHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                timestamp: _fx.Genesis.Timestamp.ToString(
                    BlockHeader.TimestampFormat,
                    CultureInfo.InvariantCulture
                ),
                preEvaluationHash: _fx.Genesis.PreEvaluationHash.ByteArray,
                stateRootHash: _fx.Genesis.StateRootHash?.ByteArray ?? ImmutableArray<byte>.Empty
            );
            Bencodex.Types.Dictionary expected = Bencodex.Types.Dictionary.Empty
                .Add(BlockHeader.IndexKey, 0)
                .Add(
                    BlockHeader.TimestampKey,
                    _fx.Genesis.Timestamp.ToString(
                        BlockHeader.TimestampFormat,
                        CultureInfo.InvariantCulture
                    )
                )
                .Add(BlockHeader.DifficultyKey, _fx.Genesis.Difficulty)
                .Add(
                    BlockHeader.TotalDifficultyKey,
                    (IValue)new Bencodex.Types.Integer(_fx.Genesis.TotalDifficulty)
                )
                .Add(BlockHeader.NonceKey, _fx.Genesis.Nonce.ToByteArray())
                .Add(BlockHeader.HashKey, _fx.Genesis.Hash.ToByteArray())
                .Add(BlockHeader.MinerKey, _fx.Genesis.Miner?.ToByteArray() ?? new byte[0])
                .Add(BlockHeader.PreEvaluationHashKey, _fx.Genesis.PreEvaluationHash.ToByteArray());
            Assert.Equal(expected, header.ToBencodex());
            Assert.Equal(expected, new BlockHeader(expected).ToBencodex());

            ImmutableArray<byte> randomHash = TestUtils.GetRandomBytes(32).ToImmutableArray();
            ImmutableArray<byte> randomHash2 = TestUtils.GetRandomBytes(32).ToImmutableArray();
            header = new BlockHeader(
                protocolVersion: 1,
                index: 1,
                difficulty: _fx.Next.Difficulty,
                totalDifficulty: _fx.Next.TotalDifficulty,
                nonce: _fx.Next.Nonce.ByteArray,
                miner: ImmutableArray<byte>.Empty,
                hash: _fx.Next.Hash.ByteArray,
                txHash: randomHash,
                previousHash: _fx.Genesis.Hash.ByteArray,
                timestamp: _fx.Next.Timestamp.ToString(
                    BlockHeader.TimestampFormat,
                    CultureInfo.InvariantCulture
                ),
                preEvaluationHash: ImmutableArray<byte>.Empty,
                stateRootHash: randomHash2
            );
            expected = Bencodex.Types.Dictionary.Empty
                .Add(BlockHeader.ProtocolVersionKey, 1)
                .Add(BlockHeader.IndexKey, 1)
                .Add(
                    BlockHeader.TimestampKey,
                    _fx.Next.Timestamp.ToString(
                        BlockHeader.TimestampFormat,
                        CultureInfo.InvariantCulture
                    )
                )
                .Add(BlockHeader.DifficultyKey, _fx.Next.Difficulty)
                .Add(
                    BlockHeader.TotalDifficultyKey,
                    (IValue)new Bencodex.Types.Integer(_fx.Next.TotalDifficulty)
                )
                .Add(BlockHeader.NonceKey, _fx.Next.Nonce.ToByteArray())
                .Add(BlockHeader.HashKey, _fx.Next.Hash.ToByteArray())
                .Add(BlockHeader.PreviousHashKey, _fx.Genesis.Hash.ToByteArray())
                .Add(BlockHeader.TxHashKey, randomHash.ToArray())
                .Add(BlockHeader.StateRootHashKey, randomHash2.ToArray());
            Assert.Equal(expected, header.ToBencodex());
            Assert.Equal(expected, new BlockHeader(expected).ToBencodex());
        }

        [Fact]
        public void ValidateValidHeader()
        {
            _fx.Genesis.Header.Validate(DateTimeOffset.UtcNow);
            _fx.Next.Header.Validate(DateTimeOffset.UtcNow);
        }

        [Fact]
        public void ValidateHash()
        {
            var header = new BlockHeader(
                protocolVersion: 0,
                index: 0,
                difficulty: _fx.Genesis.Difficulty,
                totalDifficulty: _fx.Genesis.TotalDifficulty,
                nonce: _fx.Genesis.Nonce.ByteArray,
                miner: _fx.Genesis.Miner?.ByteArray ?? ImmutableArray<byte>.Empty,
                hash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                txHash: _fx.Genesis.TxHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                previousHash: _fx.Genesis.PreviousHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                timestamp: _fx.Genesis.Timestamp.ToString(
                    BlockHeader.TimestampFormat,
                    CultureInfo.InvariantCulture
                ),
                preEvaluationHash: _fx.Genesis.PreEvaluationHash.ByteArray,
                stateRootHash: _fx.Genesis.StateRootHash?.ByteArray ?? ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockHashException>(
                () => { header.Validate(DateTime.UtcNow); });
        }

        [Fact]
        public void ValidateProtocolVersion()
        {
            var header = new BlockHeader(
                protocolVersion: -1,
                index: _fx.Next.Index,
                difficulty: _fx.Next.Difficulty,
                totalDifficulty: _fx.Next.TotalDifficulty,
                nonce: _fx.Next.Nonce.ByteArray,
                miner: _fx.Next.Miner?.ByteArray ?? ImmutableArray<byte>.Empty,
                hash: _fx.Next.Hash.ByteArray,
                txHash: _fx.Next.TxHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                previousHash: _fx.Next.PreviousHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                timestamp: _fx.Next.Timestamp.ToString(
                    BlockHeader.TimestampFormat,
                    CultureInfo.InvariantCulture
                ),
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockProtocolVersionException>(() =>
                header.Validate(DateTimeOffset.UtcNow)
            );

            header = new BlockHeader(
                protocolVersion: Block<DumbAction>.CurrentProtocolVersion + 1,
                index: _fx.Next.Index,
                difficulty: _fx.Next.Difficulty,
                totalDifficulty: _fx.Next.TotalDifficulty,
                nonce: _fx.Next.Nonce.ByteArray,
                miner: _fx.Next.Miner?.ByteArray ?? ImmutableArray<byte>.Empty,
                hash: _fx.Next.Hash.ByteArray,
                txHash: _fx.Next.TxHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                previousHash: _fx.Next.PreviousHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                timestamp: _fx.Next.Timestamp.ToString(
                    BlockHeader.TimestampFormat,
                    CultureInfo.InvariantCulture
                ),
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockProtocolVersionException>(() =>
                header.Validate(DateTimeOffset.UtcNow)
            );
        }

        [Fact]
        public void ValidateTimestamp()
        {
            DateTimeOffset now = DateTimeOffset.UtcNow;
            string future = (now + TimeSpan.FromSeconds(16))
                .ToString(BlockHeader.TimestampFormat, CultureInfo.InvariantCulture);
            BlockHeader header = MakeBlockHeader(
                protocolVersion: 0,
                index: 0,
                difficulty: 0,
                totalDifficulty: 0,
                nonce: ImmutableArray<byte>.Empty,
                previousHash: ImmutableArray<byte>.Empty,
                txHash: ImmutableArray<byte>.Empty,
                miner: ImmutableArray<byte>.Empty,
                timestamp: future,
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: TestUtils.GetRandomBytes(32).ToImmutableArray());

            Assert.Throws<InvalidBlockTimestampException>(
                () => { header.Validate(now); });

            // it's okay because 2 seconds later.
            header.Validate(now + TimeSpan.FromSeconds(2));
        }

        [Fact]
        public void ValidateNonce()
        {
            var header = new BlockHeader(
                protocolVersion: 0,
                index: _fx.Next.Index,
                difficulty: long.MaxValue,
                totalDifficulty: _fx.Genesis.TotalDifficulty + long.MaxValue,
                nonce: _fx.Next.Nonce.ByteArray,
                miner: _fx.Next.Miner?.ByteArray ?? ImmutableArray<byte>.Empty,
                hash: _fx.Next.Hash.ByteArray,
                txHash: _fx.Next.TxHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                previousHash: _fx.Next.PreviousHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                timestamp: _fx.Next.Timestamp.ToString(
                    BlockHeader.TimestampFormat,
                    CultureInfo.InvariantCulture
                ),
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockNonceException>(() =>
                header.Validate(DateTimeOffset.UtcNow));
        }

        [Fact]
        public void ValidateIndex()
        {
            var header = new BlockHeader(
                protocolVersion: 0,
                index: -1,
                difficulty: _fx.Next.Difficulty,
                totalDifficulty: _fx.Next.TotalDifficulty,
                nonce: _fx.Next.Nonce.ByteArray,
                miner: _fx.Next.Miner?.ByteArray ?? ImmutableArray<byte>.Empty,
                hash: _fx.Next.Hash.ByteArray,
                txHash: _fx.Next.TxHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                previousHash: _fx.Next.PreviousHash?.ByteArray ?? ImmutableArray<byte>.Empty,
                timestamp: _fx.Next.Timestamp.ToString(
                    BlockHeader.TimestampFormat,
                    CultureInfo.InvariantCulture
                ),
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockIndexException>(() =>
                header.Validate(DateTimeOffset.UtcNow));
        }

        [Fact]
        public void ValidateDifficulty()
        {
            DateTimeOffset now = DateTimeOffset.UtcNow;
            var genesisHeader = new BlockHeader(
                protocolVersion: 0,
                index: 0,
                difficulty: 1000,
                totalDifficulty: 1000,
                nonce: ImmutableArray<byte>.Empty,
                previousHash: ImmutableArray<byte>.Empty,
                txHash: ImmutableArray<byte>.Empty,
                hash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                miner: ImmutableArray<byte>.Empty,
                timestamp: now.ToString(BlockHeader.TimestampFormat, CultureInfo.InvariantCulture),
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockDifficultyException>(() =>
                genesisHeader.Validate(DateTimeOffset.UtcNow));

            var header1 = new BlockHeader(
                protocolVersion: 0,
                index: 10,
                difficulty: 0,
                totalDifficulty: 1000,
                nonce: ImmutableArray<byte>.Empty,
                previousHash: ImmutableArray<byte>.Empty,
                txHash: ImmutableArray<byte>.Empty,
                hash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                miner: ImmutableArray<byte>.Empty,
                timestamp: now.ToString(BlockHeader.TimestampFormat, CultureInfo.InvariantCulture),
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockDifficultyException>(() =>
                header1.Validate(DateTimeOffset.UtcNow));

            var header2 = new BlockHeader(
                protocolVersion: 0,
                index: 10,
                difficulty: 1000,
                totalDifficulty: 10,
                nonce: ImmutableArray<byte>.Empty,
                previousHash: ImmutableArray<byte>.Empty,
                txHash: ImmutableArray<byte>.Empty,
                hash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                miner: ImmutableArray<byte>.Empty,
                timestamp: now.ToString(BlockHeader.TimestampFormat, CultureInfo.InvariantCulture),
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockTotalDifficultyException>(() =>
                header2.Validate(DateTimeOffset.UtcNow));
        }

        [Fact]
        public void ValidatePreviousHash()
        {
            DateTimeOffset now = DateTimeOffset.UtcNow;
            var genesisHeader = new BlockHeader(
                protocolVersion: 0,
                index: 0,
                difficulty: 0,
                totalDifficulty: 0,
                nonce: ImmutableArray<byte>.Empty,
                previousHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                txHash: ImmutableArray<byte>.Empty,
                hash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                miner: ImmutableArray<byte>.Empty,
                timestamp: now.ToString(BlockHeader.TimestampFormat, CultureInfo.InvariantCulture),
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockPreviousHashException>(() =>
                genesisHeader.Validate(DateTimeOffset.UtcNow));

            var header = new BlockHeader(
                protocolVersion: 0,
                index: 10,
                difficulty: 1000,
                totalDifficulty: 1500,
                nonce: ImmutableArray<byte>.Empty,
                previousHash: ImmutableArray<byte>.Empty,
                txHash: ImmutableArray<byte>.Empty,
                hash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                miner: ImmutableArray<byte>.Empty,
                timestamp: now.ToString(BlockHeader.TimestampFormat, CultureInfo.InvariantCulture),
                preEvaluationHash: TestUtils.GetRandomBytes(32).ToImmutableArray(),
                stateRootHash: ImmutableArray<byte>.Empty
            );

            Assert.Throws<InvalidBlockPreviousHashException>(() =>
                genesisHeader.Validate(DateTimeOffset.UtcNow));
        }

        private BlockHeader MakeBlockHeader(
            int protocolVersion,
            long index,
            long difficulty,
            BigInteger totalDifficulty,
            ImmutableArray<byte> nonce,
            ImmutableArray<byte> previousHash,
            ImmutableArray<byte> txHash,
            ImmutableArray<byte> miner,
            string timestamp,
            ImmutableArray<byte> preEvaluationHash,
            ImmutableArray<byte> stateRootHash
        )
        {
            return new BlockHeader(
                protocolVersion: protocolVersion,
                index: index,
                timestamp: timestamp,
                nonce: nonce,
                miner: miner,
                difficulty: difficulty,
                totalDifficulty: totalDifficulty,
                previousHash: previousHash,
                txHash: txHash,
                preEvaluationHash: preEvaluationHash,
                stateRootHash: stateRootHash);
        }
    }
}
