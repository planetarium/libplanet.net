using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Security.Cryptography;
using GraphQL;
using GraphQL.Types;
using Libplanet.Blocks;
using Libplanet.Explorer.GraphTypes;
using Libplanet.Explorer.UnitTests.Common.Action;
using Libplanet.Tx;
using Xunit;
using static Libplanet.Explorer.UnitTests.GraphQLTestUtils;

namespace Libplanet.Explorer.UnitTests.GraphTypes
{
    public class BlockTypeTest
    {
        [Fact]
        public async void Query()
        {
            var block = new Block<NoOpAction>(
                1,
                1,
                1,
                new Nonce(new byte[] {0x01, 0x23, 0x45, 0x56}),
                new Address(TestUtils.GetRandomBytes(Address.Size)),
                new BlockHash(TestUtils.GetRandomBytes(HashDigest<SHA256>.Size)),
                DateTimeOffset.UtcNow,
                ImmutableArray<Transaction<NoOpAction>>.Empty,
                preEvaluationHash: new BlockHash(TestUtils.GetRandomBytes(32)),
                stateRootHash: new HashDigest<SHA256>(
                    TestUtils.GetRandomBytes(HashDigest<SHA256>.Size)));
            var query =
                @"{
                    index
                    hash
                    nonce
                    difficulty
                    totalDifficulty
                    miner
                    timestamp
                    stateRootHash
                }";

            ExecutionResult result =
                await ExecuteQueryAsync<BlockType<NoOpAction>>(query, source: block);
            Dictionary<string, object> resultData = (Dictionary<string, object>)result.Data;
            Assert.Null(result.Errors);
            Assert.Equal(block.Index, resultData["index"]);
            Assert.Equal(
                ByteUtil.Hex(block.Hash.ToByteArray()),
                resultData["hash"]);
            Assert.Equal(block.Difficulty, resultData["difficulty"]);
            Assert.Equal(
                block.TotalDifficulty,
                resultData["totalDifficulty"]);
            Assert.Equal(
                block.Miner?.ToString(),
                resultData["miner"]);
            Assert.Equal(
                ByteUtil.Hex(block.Nonce.ToByteArray()),
                resultData["nonce"]);
            Assert.Equal(
                new DateTimeOffsetGraphType().Serialize(block.Timestamp),
                resultData["timestamp"]);
            Assert.Equal(
                ByteUtil.Hex(block.StateRootHash?.ToByteArray()),
                resultData["stateRootHash"]);
        }
    }
}
