using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Globalization;
using System.Linq;
using Bencodex;
using Bencodex.Types;
using Libplanet.Action;
using Libplanet.Blocks;
using Libplanet.Crypto;
using Libplanet.Tests.Common.Action;
using Libplanet.Tx;
using Xunit;
using Xunit.Abstractions;
using static Libplanet.Tests.TestUtils;

namespace Libplanet.Tests.Blocks
{
    public class BlockTest : IClassFixture<BlockFixture>
    {
        private BlockFixture _fx;
        private ITestOutputHelper _output;

        public BlockTest(BlockFixture fixture, ITestOutputHelper output)
        {
            _fx = fixture;
            _output = output;
        }

        [Fact]
        public void Transactions()
        {
            // Creates fixtures.
            PrivateKey[] privKeys =
                Enumerable.Repeat((object)null, 5).Select(_ => new PrivateKey()).ToArray();
            var random = new System.Random();
            Transaction<DumbAction>[] txs = Enumerable.Range(0, 50)
                .Select(i => (privKeys[i % privKeys.Length], i / privKeys.Length))
                .Select(pair =>
                    Transaction<DumbAction>.Create(
                        nonce: pair.Item2,
                        privateKey: pair.Item1,
                        genesisHash: null,
                        actions: new DumbAction[0]
                    )
                )
                .OrderBy(_ => random.Next())
                .ToArray();
            var block = new Block<DumbAction>(
                index: 0,
                difficulty: 0,
                totalDifficulty: 0,
                nonce: new Nonce(new byte[0]),
                miner: null,
                previousHash: null,
                timestamp: DateTimeOffset.UtcNow,
                transactions: txs
            );

            // For transactions signed by the same signer, these should be ordered by its tx nonce.
            Address[] signers = privKeys.Select(AddressExtensions.ToAddress).ToArray();
            foreach (Address signer in signers)
            {
                IEnumerable<Transaction<DumbAction>> signersTxs =
                    block.Transactions.Where(tx => tx.Signer == signer);
                Assert.Equal(signersTxs.OrderBy(tx => tx.Nonce).ToArray(), signersTxs.ToArray());
            }
        }

        [Fact]
        public void Mine()
        {
            Assert.Equal(0, _fx.Genesis.Index);
            Assert.Equal(0, _fx.Genesis.Difficulty);
            Assert.Null(_fx.Genesis.PreviousHash);
            Assert.Equal(
                new DateTimeOffset(2018, 11, 29, 0, 0, 0, TimeSpan.Zero),
                _fx.Genesis.Timestamp
            );
            Assert.Equal(
                new Address("21744f4f08db23e044178dafb8273aeb5ebe6644"),
                _fx.Genesis.Miner);
            Assert.Equal(new Nonce(new byte[] { 0x01, 0x00, 0x00, 0x00 }), _fx.Genesis.Nonce);
            AssertBytesEqual(
                new BlockHash(
                    new byte[]
                    {
                        0xd6, 0x93, 0xda, 0x38, 0x66, 0xa3, 0x4d, 0x65, 0x9e, 0x01, 0x4f, 0x97,
                        0xc8, 0xfe, 0xb0, 0x8a, 0xfe, 0x2e, 0x97, 0xc9, 0x9e, 0x3f, 0x33, 0x89,
                        0xda, 0x02, 0x5f, 0xd0, 0x66, 0x5c, 0x62, 0x1c,
                    }
                ),
                _fx.Genesis.Hash
            );

            Block<PolymorphicAction<BaseAction>> next = MineNext(_fx.Genesis);

            Assert.Equal(1, _fx.Next.Index);
            Assert.Equal(1, _fx.Next.Difficulty);
            Assert.Equal(_fx.Genesis.Hash, _fx.Next.PreviousHash);
            Assert.Equal(
                new DateTimeOffset(2018, 11, 29, 0, 0, 15, TimeSpan.Zero),
                _fx.Next.Timestamp
            );
            Assert.Equal(
                new Address("21744f4f08db23e044178dafb8273aeb5ebe6644"),
                _fx.Next.Miner);
        }

        [Fact]
        public void ToBencodex()
        {
            byte[] expected =
            {
                0x64, 0x31, 0x3a, 0x48, 0x64, 0x31, 0x3a, 0x00, 0x69, 0x31, 0x65, 0x31, 0x3a, 0x54,
                0x69, 0x30, 0x65, 0x31, 0x3a, 0x63, 0x33, 0x32, 0x3a, 0xd6, 0x93, 0xda, 0x38, 0x66,
                0xa3, 0x4d, 0x65, 0x9e, 0x01, 0x4f, 0x97, 0xc8, 0xfe, 0xb0, 0x8a, 0xfe, 0x2e, 0x97,
                0xc9, 0x9e, 0x3f, 0x33, 0x89, 0xda, 0x02, 0x5f, 0xd0, 0x66, 0x5c, 0x62, 0x1c, 0x31,
                0x3a, 0x64, 0x69, 0x30, 0x65, 0x31, 0x3a, 0x68, 0x33, 0x32, 0x3a, 0xd6, 0x93, 0xda,
                0x38, 0x66, 0xa3, 0x4d, 0x65, 0x9e, 0x01, 0x4f, 0x97, 0xc8, 0xfe, 0xb0, 0x8a, 0xfe,
                0x2e, 0x97, 0xc9, 0x9e, 0x3f, 0x33, 0x89, 0xda, 0x02, 0x5f, 0xd0, 0x66, 0x5c, 0x62,
                0x1c, 0x31, 0x3a, 0x69, 0x69, 0x30, 0x65, 0x31, 0x3a, 0x6d, 0x32, 0x30, 0x3a, 0x21,
                0x74, 0x4f, 0x4f, 0x08, 0xdb, 0x23, 0xe0, 0x44, 0x17, 0x8d, 0xaf, 0xb8, 0x27, 0x3a,
                0xeb, 0x5e, 0xbe, 0x66, 0x44, 0x31, 0x3a, 0x6e, 0x34, 0x3a, 0x01, 0x00, 0x00, 0x00,
                0x31, 0x3a, 0x74, 0x75, 0x32, 0x37, 0x3a, 0x32, 0x30, 0x31, 0x38, 0x2d, 0x31, 0x31,
                0x2d, 0x32, 0x39, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x2e, 0x30,
                0x30, 0x30, 0x30, 0x30, 0x30, 0x5a, 0x65, 0x65,
            };

            AssertBytesEqual(expected, _fx.Genesis.Serialize());
            Assert.Equal(expected.Length, _fx.Genesis.BytesLength);
        }

        [Fact]
        public void FromBencodex()
        {
            byte[] encoded =
            {
                0x64, 0x31, 0x3a, 0x48, 0x64, 0x31, 0x3a, 0x00, 0x69, 0x31, 0x65, 0x31, 0x3a, 0x54,
                0x69, 0x32, 0x65, 0x31, 0x3a, 0x63, 0x33, 0x32, 0x3a, 0x28, 0x40, 0xe8, 0x6a, 0x27,
                0xda, 0x6e, 0x0d, 0xe6, 0x2e, 0xab, 0xab, 0x32, 0x95, 0x3e, 0x3b, 0x33, 0xf2, 0xa6,
                0x51, 0x18, 0x35, 0xf1, 0x85, 0x1a, 0x1a, 0xcc, 0x51, 0xd7, 0x71, 0xcb, 0x99, 0x31,
                0x3a, 0x64, 0x69, 0x31, 0x65, 0x31, 0x3a, 0x68, 0x33, 0x32, 0x3a, 0x28, 0x40, 0xe8,
                0x6a, 0x27, 0xda, 0x6e, 0x0d, 0xe6, 0x2e, 0xab, 0xab, 0x32, 0x95, 0x3e, 0x3b, 0x33,
                0xf2, 0xa6, 0x51, 0x18, 0x35, 0xf1, 0x85, 0x1a, 0x1a, 0xcc, 0x51, 0xd7, 0x71, 0xcb,
                0x99, 0x31, 0x3a, 0x69, 0x69, 0x32, 0x65, 0x31, 0x3a, 0x6d, 0x32, 0x30, 0x3a, 0x21,
                0x74, 0x4f, 0x4f, 0x08, 0xdb, 0x23, 0xe0, 0x44, 0x17, 0x8d, 0xaf, 0xb8, 0x27, 0x3a,
                0xeb, 0x5e, 0xbe, 0x66, 0x44, 0x31, 0x3a, 0x6e, 0x31, 0x30, 0x3a, 0x5c, 0x77, 0x74,
                0xc2, 0x39, 0x69, 0x37, 0x51, 0x87, 0xa5, 0x31, 0x3a, 0x70, 0x33, 0x32, 0x3a, 0x1b,
                0xba, 0x9f, 0xcf, 0x4c, 0x81, 0x52, 0xc8, 0x99, 0xed, 0x16, 0x74, 0xec, 0xbf, 0x4a,
                0x65, 0x71, 0xc2, 0x71, 0x92, 0x2c, 0x08, 0x84, 0xae, 0x80, 0x9f, 0x91, 0xf0, 0x37,
                0xbe, 0xd8, 0xfc, 0x31, 0x3a, 0x74, 0x75, 0x32, 0x37, 0x3a, 0x32, 0x30, 0x31, 0x38,
                0x2d, 0x31, 0x31, 0x2d, 0x32, 0x39, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x33,
                0x30, 0x2e, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x5a, 0x31, 0x3a, 0x78, 0x33, 0x32,
                0x3a, 0x75, 0xa9, 0x2b, 0xf5, 0xcf, 0xf3, 0x5d, 0x5b, 0x4d, 0x0c, 0xb8, 0x40, 0xab,
                0x61, 0x11, 0x3d, 0xee, 0xab, 0x6f, 0x78, 0x0f, 0x9b, 0x69, 0xfc, 0x48, 0x68, 0xe6,
                0xba, 0xac, 0xdc, 0xcb, 0x54, 0x65, 0x31, 0x3a, 0x54, 0x6c, 0x34, 0x33, 0x36, 0x3a,
                0x64, 0x31, 0x3a, 0x53, 0x37, 0x31, 0x3a, 0x30, 0x45, 0x02, 0x21, 0x00, 0xc4, 0xf1,
                0x85, 0x62, 0xdf, 0x1a, 0x46, 0xb0, 0x0b, 0x9c, 0x50, 0x81, 0x9f, 0x24, 0xaa, 0xf5,
                0x83, 0xc8, 0x86, 0xaa, 0x82, 0xcc, 0xb9, 0xdf, 0x27, 0x41, 0xd0, 0x21, 0xba, 0x3d,
                0xf7, 0x18, 0x02, 0x20, 0x7e, 0xb2, 0x5b, 0xbd, 0xaa, 0x3c, 0xc5, 0x2a, 0x36, 0x4c,
                0x28, 0x77, 0xbb, 0xac, 0x31, 0xb4, 0xa0, 0x22, 0xa2, 0x44, 0x97, 0xaf, 0x90, 0x5b,
                0x01, 0xff, 0x24, 0x09, 0xea, 0x85, 0x7f, 0x5c, 0x31, 0x3a, 0x61, 0x6c, 0x64, 0x75,
                0x37, 0x3a, 0x74, 0x79, 0x70, 0x65, 0x5f, 0x69, 0x64, 0x75, 0x36, 0x3a, 0x61, 0x74,
                0x74, 0x61, 0x63, 0x6b, 0x75, 0x36, 0x3a, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x73, 0x64,
                0x75, 0x36, 0x3a, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74, 0x75, 0x33, 0x3a, 0x6f, 0x72,
                0x63, 0x75, 0x31, 0x34, 0x3a, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74, 0x5f, 0x61, 0x64,
                0x64, 0x72, 0x65, 0x73, 0x73, 0x32, 0x30, 0x3a, 0xc2, 0xa8, 0x60, 0x14, 0x07, 0x3d,
                0x66, 0x2a, 0x4a, 0x9b, 0xfc, 0xf9, 0xcb, 0x54, 0x26, 0x3d, 0xfa, 0x4f, 0x5c, 0xbc,
                0x75, 0x36, 0x3a, 0x77, 0x65, 0x61, 0x70, 0x6f, 0x6e, 0x75, 0x34, 0x3a, 0x77, 0x61,
                0x6e, 0x64, 0x65, 0x65, 0x64, 0x75, 0x37, 0x3a, 0x74, 0x79, 0x70, 0x65, 0x5f, 0x69,
                0x64, 0x75, 0x35, 0x3a, 0x73, 0x6c, 0x65, 0x65, 0x70, 0x75, 0x36, 0x3a, 0x76, 0x61,
                0x6c, 0x75, 0x65, 0x73, 0x64, 0x75, 0x37, 0x3a, 0x7a, 0x6f, 0x6e, 0x65, 0x5f, 0x69,
                0x64, 0x69, 0x31, 0x30, 0x65, 0x65, 0x65, 0x65, 0x31, 0x3a, 0x67, 0x33, 0x32, 0x3a,
                0xd6, 0x93, 0xda, 0x38, 0x66, 0xa3, 0x4d, 0x65, 0x9e, 0x01, 0x4f, 0x97, 0xc8, 0xfe,
                0xb0, 0x8a, 0xfe, 0x2e, 0x97, 0xc9, 0x9e, 0x3f, 0x33, 0x89, 0xda, 0x02, 0x5f, 0xd0,
                0x66, 0x5c, 0x62, 0x1c, 0x31, 0x3a, 0x6e, 0x69, 0x30, 0x65, 0x31, 0x3a, 0x70, 0x36,
                0x35, 0x3a, 0x04, 0x46, 0x11, 0x5b, 0x01, 0x31, 0xba, 0xcc, 0xf9, 0x4a, 0x58, 0x56,
                0xed, 0xe8, 0x71, 0x29, 0x5f, 0x6f, 0x3d, 0x35, 0x2e, 0x68, 0x47, 0xcd, 0xa9, 0xc0,
                0x3e, 0x89, 0xfe, 0x09, 0xf7, 0x32, 0x80, 0x87, 0x11, 0xec, 0x97, 0xaf, 0x6e, 0x34,
                0x1f, 0x11, 0x0a, 0x32, 0x6d, 0xa1, 0xbd, 0xb8, 0x1f, 0x5a, 0xe3, 0xba, 0xdf, 0x76,
                0xa9, 0x0b, 0x22, 0xc8, 0xc4, 0x91, 0xae, 0xd3, 0xaa, 0xa2, 0x96, 0x31, 0x3a, 0x73,
                0x32, 0x30, 0x3a, 0xc2, 0xa8, 0x60, 0x14, 0x07, 0x3d, 0x66, 0x2a, 0x4a, 0x9b, 0xfc,
                0xf9, 0xcb, 0x54, 0x26, 0x3d, 0xfa, 0x4f, 0x5c, 0xbc, 0x31, 0x3a, 0x74, 0x75, 0x32,
                0x37, 0x3a, 0x32, 0x30, 0x31, 0x38, 0x2d, 0x31, 0x31, 0x2d, 0x32, 0x31, 0x54, 0x30,
                0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x2e, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
                0x5a, 0x31, 0x3a, 0x75, 0x6c, 0x32, 0x30, 0x3a, 0xc2, 0xa8, 0x60, 0x14, 0x07, 0x3d,
                0x66, 0x2a, 0x4a, 0x9b, 0xfc, 0xf9, 0xcb, 0x54, 0x26, 0x3d, 0xfa, 0x4f, 0x5c, 0xbc,
                0x65, 0x65, 0x65, 0x65,
            };

            Block<PolymorphicAction<BaseAction>> actual =
                Block<PolymorphicAction<BaseAction>>.Deserialize(encoded);
            Assert.Equal(_fx.HasTx, actual);
            Assert.Equal(actual.BytesLength, encoded.Length);
            AssertBytesEqual(_fx.HasTx.Serialize(), encoded);
            Assert.Equal(_fx.HasTx.BytesLength, encoded.Length);
        }

        [Fact]
        public void DetectInvalidProtocolVersion()
        {
            DateTimeOffset now = DateTimeOffset.UtcNow;
            Block<DumbAction> block = Block<DumbAction>.Mine(
                _fx.Next.Index,
                _fx.Next.Difficulty,
                _fx.Genesis.TotalDifficulty,
                _fx.Next.Miner.Value,
                _fx.Genesis.Hash,
                now,
                new Transaction<DumbAction>[] { },
                protocolVersion: -1
            );
            Assert.Throws<InvalidBlockProtocolVersionException>(() => block.Validate(now));

            block = Block<DumbAction>.Mine(
                _fx.Next.Index,
                _fx.Next.Difficulty,
                _fx.Genesis.TotalDifficulty,
                _fx.Next.Miner.Value,
                _fx.Genesis.Hash,
                now,
                new Transaction<DumbAction>[] { },
                protocolVersion: Block<DumbAction>.CurrentProtocolVersion + 1
            );
            Assert.Throws<InvalidBlockProtocolVersionException>(() => block.Validate(now));
        }

        [Fact]
        public void CanDetectInvalidTimestamp()
        {
            DateTimeOffset now = DateTimeOffset.UtcNow;
            var block = Block<DumbAction>.Mine(
                _fx.Next.Index,
                _fx.Next.Difficulty,
                _fx.Genesis.TotalDifficulty,
                _fx.Next.Miner.Value,
                _fx.Genesis.Hash,
                now + TimeSpan.FromSeconds(16),
                new Transaction<DumbAction>[] { }
            );

            Assert.Throws<InvalidBlockTimestampException>(
                () => { block.Validate(now); });

            // it's okay because 2 seconds later.
            block.Validate(now + TimeSpan.FromSeconds(2));
        }

        [Fact]
        public void DetectInvalidNonce()
        {
            const int easyDifficulty = 4;
            var invalidBlock = new Block<PolymorphicAction<BaseAction>>(
                index: _fx.Next.Index,
                difficulty: easyDifficulty,
                totalDifficulty: _fx.Genesis.TotalDifficulty + easyDifficulty,
                nonce: new Nonce(new byte[] { 0x00 }),
                miner: _fx.Next.Miner,
                previousHash: _fx.Next.PreviousHash,
                timestamp: _fx.Next.Timestamp,
                transactions: _fx.Next.Transactions,
                preEvaluationHash: _fx.Next.PreEvaluationHash,
                protocolVersion: _fx.Next.ProtocolVersion
            );

            Assert.Throws<InvalidBlockNonceException>(() =>
                invalidBlock.Validate(DateTimeOffset.UtcNow));
        }

        [Fact]
        public void DetectInvalidDifficulty()
        {
            var invalidDifficultyGenesis = new Block<DumbAction>(
                index: _fx.Genesis.Index,
                difficulty: 1, // invalid
                totalDifficulty: 1,
                nonce: _fx.Genesis.Nonce,
                miner: _fx.Genesis.Miner,
                previousHash: _fx.Genesis.PreviousHash,
                timestamp: _fx.Genesis.Timestamp,
                transactions: MineGenesis<DumbAction>().Transactions
            );
            Assert.Throws<InvalidBlockDifficultyException>(() =>
                invalidDifficultyGenesis.Validate(DateTimeOffset.UtcNow)
            );

            var invalidTotalDifficultyGenesis = new Block<DumbAction>(
                index: _fx.Genesis.Index,
                difficulty: 0,
                totalDifficulty: 1, // invalid
                nonce: _fx.Genesis.Nonce,
                miner: _fx.Genesis.Miner,
                previousHash: _fx.Genesis.PreviousHash,
                timestamp: _fx.Genesis.Timestamp,
                transactions: MineGenesis<DumbAction>().Transactions
            );
            Assert.Throws<InvalidBlockTotalDifficultyException>(() =>
                invalidTotalDifficultyGenesis.Validate(DateTimeOffset.UtcNow)
            );

            var invalidDifficultyNext = new Block<PolymorphicAction<BaseAction>>(
                index: _fx.Next.Index,
                difficulty: 0, // invalid,
                totalDifficulty: _fx.Genesis.TotalDifficulty,
                nonce: _fx.Next.Nonce,
                miner: _fx.Next.Miner,
                previousHash: _fx.Next.PreviousHash,
                timestamp: _fx.Next.Timestamp,
                transactions: _fx.Next.Transactions
            );
            Assert.Throws<InvalidBlockDifficultyException>(() =>
                invalidDifficultyNext.Validate(DateTimeOffset.UtcNow)
            );

            var invalidTotalDifficultyNext = new Block<PolymorphicAction<BaseAction>>(
                index: _fx.Next.Index,
                difficulty: 1,
                totalDifficulty: 0,
                nonce: _fx.Next.Nonce,
                miner: _fx.Next.Miner,
                previousHash: _fx.Next.PreviousHash,
                timestamp: _fx.Next.Timestamp,
                transactions: _fx.Next.Transactions
            );
            Assert.Throws<InvalidBlockTotalDifficultyException>(() =>
                invalidTotalDifficultyNext.Validate(DateTimeOffset.UtcNow)
            );
        }

        [Fact]
        public void DetectInvalidPreviousHash()
        {
            var invalidGenesis = new Block<DumbAction>(
                index: _fx.Genesis.Index,
                difficulty: _fx.Genesis.Difficulty,
                totalDifficulty: _fx.Genesis.TotalDifficulty,
                nonce: _fx.Genesis.Nonce,
                miner: _fx.Genesis.Miner,
                previousHash: new BlockHash(GetRandomBytes(32)), // invalid
                timestamp: _fx.Genesis.Timestamp,
                transactions: MineGenesis<DumbAction>().Transactions
            );

            Assert.Throws<InvalidBlockPreviousHashException>(() =>
                invalidGenesis.Validate(DateTimeOffset.UtcNow)
            );

            var invalidNext = new Block<PolymorphicAction<BaseAction>>(
                index: _fx.Next.Index,
                difficulty: _fx.Next.Difficulty,
                totalDifficulty: _fx.Next.TotalDifficulty,
                nonce: _fx.Next.Nonce,
                miner: _fx.Next.Miner,
                previousHash: null,
                timestamp: _fx.Next.Timestamp,
                transactions: _fx.Next.Transactions
            );

            Assert.Throws<InvalidBlockPreviousHashException>(() =>
                invalidNext.Validate(DateTimeOffset.UtcNow)
            );
        }

        [Fact]
        public void ConvertToRaw()
        {
            RawBlock rawGenesis = _fx.Genesis.ToRawBlock();
            Assert.Equal(0, rawGenesis.Header.Index);
            Assert.Equal(0, rawGenesis.Header.Difficulty);
            Assert.Empty(rawGenesis.Header.PreviousHash);
            Assert.Equal("2018-11-29T00:00:00.000000Z", rawGenesis.Header.Timestamp);
            Assert.Equal(
                ByteUtil.ParseHex("21744f4f08db23e044178dafb8273aeb5ebe6644"),
                rawGenesis.Header.Miner
            );
            Assert.Empty(rawGenesis.Transactions);
            Assert.Empty(rawGenesis.Header.TxHash);
            Assert.Equal(
                new byte[] { 0x01, 0x00, 0x00, 0x00 },
                rawGenesis.Header.Nonce
            );
            AssertBytesEqual(
                new byte[32]
                {
                    0xd6, 0x93, 0xda, 0x38, 0x66, 0xa3, 0x4d, 0x65, 0x9e, 0x01, 0x4f, 0x97,
                    0xc8, 0xfe, 0xb0, 0x8a, 0xfe, 0x2e, 0x97, 0xc9, 0x9e, 0x3f, 0x33, 0x89,
                    0xda, 0x02, 0x5f, 0xd0, 0x66, 0x5c, 0x62, 0x1c,
                },
                rawGenesis.Header.Hash.ToArray()
            );

            RawBlock rawNext = _fx.Next.ToRawBlock();

            Assert.Equal(1, rawNext.Header.Index);
            Assert.Equal(1, rawNext.Header.Difficulty);
            Assert.Equal(rawGenesis.Header.Hash.ToArray(), rawNext.Header.PreviousHash.ToArray());
            Assert.Equal("2018-11-29T00:00:15.000000Z", rawNext.Header.Timestamp);
            Assert.Equal(
                ByteUtil.ParseHex("21744f4f08db23e044178dafb8273aeb5ebe6644"),
                rawNext.Header.Miner
            );
            Assert.Empty(rawNext.Transactions);
            Assert.Empty(rawNext.Header.TxHash);
            AssertBytesEqual(
                new byte[]
                {
                    0x1b, 0xba, 0x9f, 0xcf, 0x4c, 0x81, 0x52, 0xc8, 0x99, 0xed, 0x16, 0x74, 0xec,
                    0xbf, 0x4a, 0x65, 0x71, 0xc2, 0x71, 0x92, 0x2c, 0x08, 0x84, 0xae, 0x80, 0x9f,
                    0x91, 0xf0, 0x37, 0xbe, 0xd8, 0xfc,
                },
                rawNext.Header.Hash.ToArray()
            );

            RawBlock rawHasText = _fx.HasTx.ToRawBlock();

            Assert.Equal(2, rawHasText.Header.Index);
            Assert.Equal(1, rawHasText.Header.Difficulty);
            Assert.Equal(rawNext.Header.Hash.ToArray(), rawHasText.Header.PreviousHash.ToArray());
            Assert.Equal("2018-11-29T00:00:30.000000Z", rawHasText.Header.Timestamp);
            Assert.Equal(
                ByteUtil.ParseHex("21744f4f08db23e044178dafb8273aeb5ebe6644"),
                rawHasText.Header.Miner
            );
            Assert.Single(rawHasText.Transactions);
            AssertBytesEqual(
                new byte[]
                {
                    0x75, 0xa9, 0x2b, 0xf5, 0xcf, 0xf3, 0x5d, 0x5b, 0x4d, 0x0c, 0xb8, 0x40, 0xab,
                    0x61, 0x11, 0x3d, 0xee, 0xab, 0x6f, 0x78, 0x0f, 0x9b, 0x69, 0xfc, 0x48, 0x68,
                    0xe6, 0xba, 0xac, 0xdc, 0xcb, 0x54,
                },
                rawHasText.Header.TxHash.ToArray()
            );
            AssertBytesEqual(
                new byte[32]
                {
                    0x28, 0x40, 0xe8, 0x6a, 0x27, 0xda, 0x6e, 0x0d, 0xe6, 0x2e, 0xab, 0xab, 0x32,
                    0x95, 0x3e, 0x3b, 0x33, 0xf2, 0xa6, 0x51, 0x18, 0x35, 0xf1, 0x85, 0x1a, 0x1a,
                    0xcc, 0x51, 0xd7, 0x71, 0xcb, 0x99,
                },
                rawHasText.Header.Hash.ToArray()
            );
        }

        [Fact]
        public void CanCompareToOtherBlock()
        {
            Block<PolymorphicAction<BaseAction>> sameBlock1 = _fx.Genesis;
            var sameBlock2 = new Block<PolymorphicAction<BaseAction>>(
                index: sameBlock1.Index,
                difficulty: sameBlock1.Difficulty,
                totalDifficulty: sameBlock1.TotalDifficulty,
                nonce: sameBlock1.Nonce,
                miner: sameBlock1.Miner,
                previousHash: null,
                timestamp: sameBlock1.Timestamp,
                transactions: sameBlock1.Transactions
            );
            Block<PolymorphicAction<BaseAction>> differentBlock = _fx.Next;

            Assert.Equal(sameBlock1, sameBlock2);
            Assert.NotEqual(sameBlock2, differentBlock);

            Assert.True(sameBlock1.Equals(sameBlock2));
            Assert.False(sameBlock2.Equals(differentBlock));
        }

        [Fact]
        public void BlockStructureSize()
        {
            var emptyBlock = _fx.Next;
            var txBlock = _fx.HasTx;
            var codec = new Codec();
            // Case of a block with no any txs, contained state root.
            // Size of RawBlock
            Assert.Equal(214, emptyBlock.Serialize().Length);
            // Size of BlockDigest
            Assert.Equal(214, emptyBlock.ToBlockDigest().Serialize().Length);
            // Size of BlockHeader
            Assert.Equal(209, codec.Encode(emptyBlock.Header.ToBencodex()).Length);

            // Case of a block with txs, not contained state root.
            // Size of RawBlock
            Assert.Equal(704, txBlock.Serialize().Length);
            // Size of BlockDigest
            Assert.Equal(299, txBlock.ToBlockDigest().Serialize().Length);
            // Size of BlockHeader
            Assert.Equal(254, codec.Encode(txBlock.Header.ToBencodex()).Length);
        }

        [Fact]
        public void OrderTxsForEvaluation()
        {
            const int protocolVersion = 1;
            const int numSigners = 5;
            const int numTxsPerSigner = 3;

            ImmutableArray<PrivateKey> signers = ImmutableArray.Create(new PrivateKey[]
                {
                    _fx.TxFixture.PrivateKey1,
                    _fx.TxFixture.PrivateKey2,
                    _fx.TxFixture.PrivateKey3,
                    _fx.TxFixture.PrivateKey4,
                    _fx.TxFixture.PrivateKey5,
                });
            ImmutableArray<ImmutableArray<int>> noncesPerSigner = ImmutableArray.Create(
                new ImmutableArray<int>[]
                    {
                        ImmutableArray.Create(new int[] { 0, 2, 1 }),
                        ImmutableArray.Create(new int[] { 1, 0, 2 }),
                        ImmutableArray.Create(new int[] { 1, 2, 0 }),
                        ImmutableArray.Create(new int[] { 2, 0, 1 }),
                        ImmutableArray.Create(new int[] { 2, 1, 0 }),
                    });
            // Unix Epoch used for hard coded timestamp.
            ImmutableArray<Transaction<RandomAction>> txs =
                signers.Zip(noncesPerSigner, (signer, nonces) => (signer, nonces))
                    .SelectMany(
                        signerNoncesPair => signerNoncesPair.nonces,
                        (signerNoncesPair, nonce) => (signerNoncesPair.signer, nonce))
                    .Select(signerNoncePair => Transaction<RandomAction>.Create(
                        nonce: signerNoncePair.nonce,
                        privateKey: signerNoncePair.signer,
                        genesisHash: null,
                        actions: new[] { new RandomAction(signerNoncePair.signer.ToAddress()) },
                        timestamp: DateTimeOffset.UnixEpoch)).ToImmutableArray();
            // Rearrange transactions so that transactions are not grouped by signers
            // while keeping the hard coded mixed order nonces above.
            txs = txs
                .Where((tx, i) => i % numTxsPerSigner == 0)
                .Concat(txs.Where((tx, i) => i % numTxsPerSigner != 0)).ToImmutableArray();
            byte[] preEvaluationHashBytes =
            {
                0x45, 0xa2, 0x21, 0x87, 0xe2, 0xd8, 0x85, 0x0b, 0xb3, 0x57,
                0x88, 0x69, 0x58, 0xbc, 0x3e, 0x85, 0x60, 0x92, 0x9c, 0xcc,
            };
            BlockHash blockHash = new BlockHash(preEvaluationHashBytes);

            var orderedTxs = Block<RandomAction>.OrderTxsForEvaluation(
                protocolVersion: protocolVersion,
                txs: txs,
                preEvaluationHash: blockHash).ToImmutableArray();

            // Check signers are grouped together.
            for (int i = 0; i < numSigners; i++)
            {
                var signerTxs = orderedTxs.Skip(i * numTxsPerSigner).Take(numTxsPerSigner);
                Assert.True(signerTxs.Select(tx => tx.Signer).Distinct().Count() == 1);
            }

            // Check nonces are ordered.
            foreach (var signer in signers)
            {
                var signerTxs = orderedTxs.Where(tx => tx.Signer == signer.ToAddress());
                Assert.Equal(signerTxs.OrderBy(tx => tx.Nonce).ToArray(), signerTxs.ToArray());
            }

            string[] originalAddresses =
            {
                "0xc2A86014073D662a4a9bFCF9CB54263dfa4F5cBc",
                "0x921Ba81C0be280C8A2faed79E14aD2a098874759",
                "0x1d2B31bF9A2CA71051f8c66E1C783Ae70EF32798",
                "0xfcbfa4977B2Fc7A608E4Bd2F6F0D6b27C0a4cd13",
                "0xB0ea0018Ab647418FA81c384194C9167e6A3C925",
            };
            string[] orderedAddresses =
            {
                "0x921Ba81C0be280C8A2faed79E14aD2a098874759",
                "0x1d2B31bF9A2CA71051f8c66E1C783Ae70EF32798",
                "0xB0ea0018Ab647418FA81c384194C9167e6A3C925",
                "0xfcbfa4977B2Fc7A608E4Bd2F6F0D6b27C0a4cd13",
                "0xc2A86014073D662a4a9bFCF9CB54263dfa4F5cBc",
            };

            Assert.True(originalAddresses.SequenceEqual(
                signers.Select(signer => signer.ToAddress().ToString())));
            Assert.True(orderedAddresses.SequenceEqual(
                orderedTxs
                    .Where((tx, i) => i % numTxsPerSigner == 0)
                    .Select(tx => tx.Signer.ToString())));
        }

        [Fact]
        public void TransactionOrderIdempotent()
        {
            const int signerCount = 5;
            DateTimeOffset timestamp = DateTimeOffset.UtcNow;
            var signers = Enumerable.Range(0, signerCount).Select(_ => new PrivateKey());
            ImmutableArray<Transaction<RandomAction>> txs = signers.Select(signer =>
                Transaction<RandomAction>.Create(
                    0,
                    signer,
                    null,
                    new[] { new RandomAction(signer.ToAddress()) })).ToImmutableArray();
            var blockA = MineGenesis(timestamp: timestamp, transactions: txs);
            var blockB = MineGenesis(timestamp: timestamp, transactions: txs);

            Assert.True(blockA.Transactions.SequenceEqual(blockB.Transactions));
        }

        [Fact]
        public void BytesLength()
        {
            var block = new Block<DumbAction>(
                index: 0,
                difficulty: 0,
                totalDifficulty: 0,
                nonce: new Nonce(new byte[0]),
                miner: null,
                previousHash: null,
                timestamp: DateTimeOffset.UtcNow,
                transactions: new Transaction<DumbAction>[0]
            );
            Assert.Equal(146, block.BytesLength);
        }

        [Fact]
        public void ValidateTxHash()
        {
            Transaction<DumbAction>[] txs = new[]
            {
                Transaction<DumbAction>.Create(0, new PrivateKey(), null, new DumbAction[0]),
                Transaction<DumbAction>.Create(0, new PrivateKey(), null, new DumbAction[0]),
                Transaction<DumbAction>.Create(0, new PrivateKey(), null, new DumbAction[0]),
            };
            var block = new Block<DumbAction>(
                index: 0,
                difficulty: 0,
                totalDifficulty: 0,
                nonce: new Nonce(new byte[0]),
                miner: null,
                previousHash: null,
                timestamp: DateTimeOffset.UtcNow,
                transactions: txs
            );

            block.Validate(DateTimeOffset.UtcNow);

            Dictionary blockDict = block.ToBencodex();
            var txList = (List)blockDict[RawBlock.TransactionsKey];

            var abnormalTxs = new Block<DumbAction>(
                blockDict.SetItem(
                    RawBlock.TransactionsKey,
                    (IValue)new List(txList.Take(2))
                )
            );

            var exc = Assert.Throws<InvalidBlockTxHashException>(
                () => abnormalTxs.Validate(DateTimeOffset.UtcNow)
            );
            Assert.Equal(abnormalTxs.TxHash, exc.BlockTxHash);

            var emptyTxs = new Block<DumbAction>(
                blockDict.SetItem(
                    RawBlock.TransactionsKey,
                    (IValue)default(List)
                )
            );
            Assert.Throws<InvalidBlockTxHashException>(
                 () => emptyTxs.Validate(DateTimeOffset.UtcNow)
            );
        }

        [Fact]
        public void DetectInvalidPreEvaluationHash()
        {
            var invalidBlock = new Block<PolymorphicAction<BaseAction>>(
                index: _fx.Next.Index,
                difficulty: _fx.Next.Difficulty,
                totalDifficulty: _fx.Next.TotalDifficulty * 10000, // invalid
                preEvaluationHash: _fx.Next.PreEvaluationHash,
                nonce: new Nonce(new byte[] { 0x00 }),
                miner: _fx.Next.Miner,
                previousHash: _fx.Next.PreviousHash,
                timestamp: _fx.Next.Timestamp,
                transactions: _fx.Next.Transactions);

            Assert.Throws<InvalidBlockPreEvaluationHashException>(() =>
                invalidBlock.Validate(DateTimeOffset.UtcNow));
        }

        [Fact]
        public void DetectInvalidTxSignature()
        {
            RawTransaction rawTx = new RawTransaction(
                0,
                _fx.TxFixture.Address1.ByteArray,
                _fx.Genesis.Hash.ByteArray,
                ImmutableArray<ImmutableArray<byte>>.Empty,
                _fx.TxFixture.PublicKey1.Format(false).ToImmutableArray(),
                DateTimeOffset.UtcNow.ToString(
                    "yyyy-MM-ddTHH:mm:ss.ffffffZ",
                    CultureInfo.InvariantCulture
                ),
                ImmutableArray<IValue>.Empty,
                new byte[10].ToImmutableArray()
            );
            var invalidTx = new Transaction<DumbAction>(rawTx);
            Assert.Throws<InvalidTxSignatureException>(() =>
                MineNext(
                    MineGenesis<DumbAction>(),
                    new List<Transaction<DumbAction>>
                    {
                        invalidTx,
                    }
                )
            );
        }

        [Fact]
        public void DetectInvalidTxPublicKey()
        {
            RawTransaction rawTxWithoutSig = new RawTransaction(
                0,
                new PrivateKey().ToAddress().ByteArray,
                _fx.Genesis.Hash.ByteArray,
                ImmutableArray<ImmutableArray<byte>>.Empty,
                _fx.TxFixture.PublicKey1.Format(false).ToImmutableArray(),
                DateTimeOffset.UtcNow.ToString(
                    "yyyy-MM-ddTHH:mm:ss.ffffffZ",
                    CultureInfo.InvariantCulture
                ),
                ImmutableArray<IValue>.Empty,
                ImmutableArray<byte>.Empty
            );
            byte[] sig = _fx.TxFixture.PrivateKey1.Sign(
                new Transaction<DumbAction>(rawTxWithoutSig).Serialize(false)
            );
            var invalidTx = new Transaction<DumbAction>(
                new RawTransaction(
                    0,
                    rawTxWithoutSig.Signer,
                    rawTxWithoutSig.GenesisHash,
                    rawTxWithoutSig.UpdatedAddresses,
                    rawTxWithoutSig.PublicKey,
                    rawTxWithoutSig.Timestamp,
                    rawTxWithoutSig.Actions,
                    sig.ToImmutableArray()
                )
            );
            Assert.Throws<InvalidTxPublicKeyException>(() =>
                MineNext(
                    MineGenesis<DumbAction>(),
                    new List<Transaction<DumbAction>>
                    {
                        invalidTx,
                    }
                )
            );
        }
    }
}
