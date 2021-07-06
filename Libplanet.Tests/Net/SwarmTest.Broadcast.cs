using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Security.Cryptography;
using System.Threading;
using System.Threading.Tasks;
using Libplanet.Blockchain;
using Libplanet.Blockchain.Policies;
using Libplanet.Blockchain.Renderers;
using Libplanet.Blockchain.Renderers.Debug;
using Libplanet.Blocks;
using Libplanet.Crypto;
using Libplanet.Net;
using Libplanet.Net.Messages;
using Libplanet.Net.Transports;
using Libplanet.Store;
using Libplanet.Tests.Common.Action;
using Libplanet.Tests.Store;
using Libplanet.Tests.Store.Trie;
using Libplanet.Tx;
using Serilog;
using Serilog.Events;
using xRetry;
using Xunit;

namespace Libplanet.Tests.Net
{
    public partial class SwarmTest
    {
        [Fact(Timeout = Timeout)]
        public async Task BroadcastBlockToReconnectedPeer()
        {
            Swarm<DumbAction> seed = CreateSwarm();
            BlockChain<DumbAction> chainWithBlocks = seed.BlockChain;

            var privateKey = new PrivateKey();
            Swarm<DumbAction> swarmA = CreateSwarm(privateKey: privateKey);
            Swarm<DumbAction> swarmB = CreateSwarm(privateKey: privateKey);

            foreach (int i in Enumerable.Range(0, 10))
            {
                await chainWithBlocks.MineBlock(seed.Address);
            }

            try
            {
                await StartAsync(seed);
                await StartAsync(swarmA);
                await StartAsync(swarmB);

                Assert.Equal(swarmA.AsPeer, swarmB.AsPeer);

                await swarmA.AddPeersAsync(new[] { seed.AsPeer }, null);
                await StopAsync(swarmA);
                await seed.PeerDiscovery.RefreshTableAsync(
                    TimeSpan.Zero,
                    default(CancellationToken));

                Assert.DoesNotContain(swarmA.AsPeer, seed.Peers);

                await swarmB.AddPeersAsync(new[] { seed.AsPeer }, null);

                // This is added for context switching.
                await Task.Delay(100);

                Assert.Contains(swarmB.AsPeer, seed.Peers);
                Assert.Contains(seed.AsPeer, swarmB.Peers);

                seed.BroadcastBlock(chainWithBlocks.Tip);

                await swarmB.BlockAppended.WaitAsync();

                Assert.NotEqual(chainWithBlocks.BlockHashes, swarmA.BlockChain.BlockHashes);
                Assert.Equal(chainWithBlocks.BlockHashes, swarmB.BlockChain.BlockHashes);
            }
            finally
            {
                await StopAsync(seed);
                await StopAsync(swarmA);
                await StopAsync(swarmB);

                seed.Dispose();
                swarmA.Dispose();
                swarmB.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BroadcastIgnoreFromDifferentGenesisHash()
        {
            Swarm<DumbAction> receiverSwarm = CreateSwarm();
            BlockChain<DumbAction> receiverChain = receiverSwarm.BlockChain;
            var invalidGenesisBlock = new Block<DumbAction>(
                0,
                0,
                0,
                new Nonce(new byte[] { 0x10, 0x00, 0x00, 0x00 }),
                receiverSwarm.Address,
                null,
                DateTimeOffset.MinValue,
                ImmutableArray<Transaction<DumbAction>>.Empty,
                HashAlgorithmType.Of<SHA256>()
            );
            BlockChain<DumbAction> seedChain = TestUtils.MakeBlockChain(
                receiverChain.Policy,
                new DefaultStore(path: null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore()),
                genesisBlock: invalidGenesisBlock);
            Swarm<DumbAction> seedSwarm = CreateSwarm(seedChain);
            try
            {
                await StartAsync(receiverSwarm);
                await StartAsync(seedSwarm);

                await receiverSwarm.AddPeersAsync(new[] { seedSwarm.AsPeer }, null);
                Block<DumbAction> block = await seedChain.MineBlock(seedSwarm.Address);
                seedSwarm.BroadcastBlock(block);
                while (receiverSwarm.Transport.MessageHistory
                    .Any(msg => msg is BlockHeaderMessage))
                {
                    await Task.Delay(100);
                }

                await Task.Delay(100);
                Assert.NotEqual(seedChain.Tip, receiverChain.Tip);
            }
            finally
            {
                await StopAsync(seedSwarm);
                await StopAsync(receiverSwarm);

                seedSwarm.Dispose();
            }
        }

        [RetryFact(10, Timeout = Timeout)]
        public async Task BroadcastWhileMining()
        {
            Swarm<DumbAction> a = CreateSwarm();
            Swarm<DumbAction> b = CreateSwarm();

            BlockChain<DumbAction> chainA = a.BlockChain;
            BlockChain<DumbAction> chainB = b.BlockChain;

            Task CreateMiner(
                Swarm<DumbAction> swarm,
                BlockChain<DumbAction> chain,
                int delay,
                CancellationToken cancellationToken
            )
            {
                return Task.Run(async () =>
                {
                    while (!cancellationToken.IsCancellationRequested)
                    {
                        try
                        {
                            var block = await chain.MineBlock(swarm.Address);

                            Log.Debug(
                                "Block mined. [Node: {0}, Block: {1}]",
                                swarm.Address,
                                block.Hash);
                            swarm.BroadcastBlock(block);
                        }
                        catch (OperationCanceledException)
                        {
                            continue;
                        }
                        finally
                        {
                            await Task.Delay(delay);
                        }
                    }

                    swarm.BroadcastBlock(chain[-1]);
                    Log.Debug("Mining complete.");
                });
            }

            try
            {
                await StartAsync(a);
                await StartAsync(b);

                await a.AddPeersAsync(new[] { b.AsPeer }, null);

                var minerCanceller = new CancellationTokenSource();
                Task miningA = CreateMiner(a, chainA, 5000, minerCanceller.Token);
                Task miningB = CreateMiner(b, chainB, 8000, minerCanceller.Token);

                await Task.Delay(10000);
                minerCanceller.Cancel();

                await Task.WhenAll(miningA, miningB);

                await Task.Delay(5000);
            }
            finally
            {
                await StopAsync(a);
                await StopAsync(b);
            }

            _logger.CompareBothChains(LogEventLevel.Debug, "A", chainA, "B", chainB);
            Assert.Equal(chainA.BlockHashes, chainB.BlockHashes);
        }

        [Fact(Timeout = Timeout)]
        public async Task BroadcastTx()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();
            Swarm<DumbAction> swarmC = CreateSwarm();

            BlockChain<DumbAction> chainA = swarmA.BlockChain;
            BlockChain<DumbAction> chainB = swarmB.BlockChain;
            BlockChain<DumbAction> chainC = swarmC.BlockChain;

            Transaction<DumbAction> tx = Transaction<DumbAction>.Create(
                0,
                new PrivateKey(),
                chainA.Genesis.Hash,
                new DumbAction[] { }
            );

            chainA.StageTransaction(tx);
            await chainA.MineBlock(swarmA.Address);

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await StartAsync(swarmC);

                await swarmA.AddPeersAsync(new[] { swarmB.AsPeer }, null);
                await swarmB.AddPeersAsync(new[] { swarmC.AsPeer }, null);
                await swarmC.AddPeersAsync(new[] { swarmA.AsPeer }, null);

                swarmA.BroadcastTxs(new[] { tx });

                await swarmC.TxReceived.WaitAsync();
                await swarmB.TxReceived.WaitAsync();

                Assert.Equal(tx, chainB.GetTransaction(tx.Id));
                Assert.Equal(tx, chainC.GetTransaction(tx.Id));
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
                await StopAsync(swarmC);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BroadcastTxWhileMining()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmC = CreateSwarm();

            BlockChain<DumbAction> chainA = swarmA.BlockChain;
            BlockChain<DumbAction> chainC = swarmC.BlockChain;

            var privateKey = new PrivateKey();
            var address = privateKey.ToAddress();
            var txCount = 10;

            var txs = Enumerable.Range(0, txCount).Select(_ =>
                    chainA.MakeTransaction(
                        new PrivateKey(),
                        new[] { new DumbAction(address, "foo") }))
                .ToArray();

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmC);

                await swarmC.AddPeersAsync(new[] { swarmA.AsPeer }, null);
                Assert.Contains(swarmC.AsPeer, swarmA.Peers);
                Assert.Contains(swarmA.AsPeer, swarmC.Peers);

                for (var i = 0; i < 100; i++)
                {
                    swarmA.BroadcastTxs(txs);
                }

                var t = Task.Run(async () =>
                {
                    for (var i = 0; i < 10; i++)
                    {
                        await chainC.MineBlock(swarmC.Address);
                    }
                });

                while (!chainC.GetStagedTransactionIds().Any())
                {
                    await swarmC.TxReceived.WaitAsync();
                }

                await t;

                for (var i = 0; i < txCount; i++)
                {
                    Assert.NotNull(chainC.GetTransaction(txs[i].Id));
                }
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmC);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BroadcastTxAsync()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();
            Swarm<DumbAction> swarmC = CreateSwarm();

            BlockChain<DumbAction> chainA = swarmA.BlockChain;
            BlockChain<DumbAction> chainB = swarmB.BlockChain;
            BlockChain<DumbAction> chainC = swarmC.BlockChain;

            Transaction<DumbAction> tx = Transaction<DumbAction>.Create(
                0,
                new PrivateKey(),
                chainA.Genesis.Hash,
                new DumbAction[] { }
            );

            chainA.StageTransaction(tx);

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await StartAsync(swarmC);

                // Broadcast tx swarmA to swarmB
                await swarmA.AddPeersAsync(new[] { swarmB.AsPeer }, null);

                await swarmB.TxReceived.WaitAsync();
                Assert.Equal(tx, chainB.GetTransaction(tx.Id));

                await StopAsync(swarmA);

                // Re-Broadcast received tx swarmB to swarmC
                await swarmB.AddPeersAsync(new[] { swarmC.AsPeer }, null);

                await swarmC.TxReceived.WaitAsync();
                Assert.Equal(tx, chainC.GetTransaction(tx.Id));
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
                await StopAsync(swarmC);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BroadcastTxAsyncMany()
        {
            int size = 5;

            var policy = new BlockPolicy<DumbAction>();
            StoreFixture[] fxs = new StoreFixture[size];
            BlockChain<DumbAction>[] blockChains = new BlockChain<DumbAction>[size];
            Swarm<DumbAction>[] swarms = new Swarm<DumbAction>[size];

            for (int i = 0; i < size; i++)
            {
                fxs[i] = new DefaultStoreFixture(memory: true);
                blockChains[i] = new BlockChain<DumbAction>(
                    policy,
                    new VolatileStagePolicy<DumbAction>(),
                    fxs[i].Store,
                    fxs[i].StateStore,
                    fxs[i].GenesisBlock
                );
                swarms[i] = CreateSwarm(blockChains[i]);
            }

            Transaction<DumbAction> tx = Transaction<DumbAction>.Create(
                0,
                new PrivateKey(),
                blockChains[size - 1].Genesis.Hash,
                new DumbAction[] { }
            );

            blockChains[size - 1].StageTransaction(tx);

            try
            {
                for (int i = 0; i < size; i++)
                {
                    await StartAsync(swarms[i]);
                }

                List<Task> tasks = new List<Task>();
                for (int i = 1; i < size; i++)
                {
                    await BootstrapAsync(swarms[i], swarms[0].AsPeer);
                }

                for (int i = 0; i < size - 1; i++)
                {
                    tasks.Add(swarms[i].TxReceived.WaitAsync());
                }

                await Task.WhenAll(tasks);

                for (int i = 0; i < size; i++)
                {
                    Assert.Equal(tx, blockChains[i].GetTransaction(tx.Id));
                }
            }
            finally
            {
                for (int i = 0; i < size; i++)
                {
                    await StopAsync(swarms[i]);
                    fxs[i].Dispose();
                    swarms[i].Dispose();
                }
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task DoNotRebroadcastTxsWithLowerNonce()
        {
            // If the bucket stored peers are the same, the block may not propagate,
            // so specify private keys to make the buckets different.
            var keyA = ByteUtil.ParseHex(
                "8568eb6f287afedece2c7b918471183db0451e1a61535bb0381cfdf95b85df20");
            var keyB = ByteUtil.ParseHex(
                "c34f7498befcc39a14f03b37833f6c7bb78310f1243616524eda70e078b8313c");
            var keyC = ByteUtil.ParseHex(
                "941bc2edfab840d79914d80fe3b30840628ac37a5d812d7f922b5d2405a223d3");

            var minerKey = new PrivateKey(keyB);
            var swarmA = CreateSwarm(new PrivateKey(keyA));
            var swarmB = CreateSwarm(minerKey);
            var swarmC = CreateSwarm(new PrivateKey(keyC));

            BlockChain<DumbAction> chainA = swarmA.BlockChain;
            BlockChain<DumbAction> chainB = swarmB.BlockChain;
            BlockChain<DumbAction> chainC = swarmC.BlockChain;

            var privateKey = new PrivateKey();

            try
            {
                var tx1 = swarmA.BlockChain.MakeTransaction(
                    privateKey: privateKey,
                    actions: new DumbAction[] { });
                var tx2 = swarmA.BlockChain.MakeTransaction(
                    privateKey: privateKey,
                    actions: new DumbAction[] { });
                Assert.Equal(0, tx1.Nonce);
                Assert.Equal(1, tx2.Nonce);
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await swarmA.AddPeersAsync(new[] { swarmB.AsPeer }, null);
                swarmA.BroadcastTxs(new[] { tx1, tx2 });
                await swarmB.TxReceived.WaitAsync();
                Assert.Equal(
                    new HashSet<TxId> { tx1.Id, tx2.Id },
                    chainB.GetStagedTransactionIds().ToHashSet());

                chainA.UnstageTransaction(tx2);
                Assert.Equal(1, chainA.GetNextTxNonce(privateKey.ToAddress()));
                swarmA.RoutingTable.RemovePeer((BoundPeer)swarmB.AsPeer);
                swarmB.RoutingTable.RemovePeer((BoundPeer)swarmA.AsPeer);
                Assert.Empty(swarmA.Peers);
                Assert.Empty(swarmB.Peers);
                await chainB.MineBlock(minerKey.ToAddress());

                var tx3 = chainA.MakeTransaction(
                    privateKey: privateKey,
                    actions: new DumbAction[] { });
                var tx4 = chainA.MakeTransaction(
                    privateKey: privateKey,
                    actions: new DumbAction[] { });
                Assert.Equal(1, tx3.Nonce);
                Assert.Equal(2, tx4.Nonce);

                await StartAsync(swarmC);
                await swarmA.AddPeersAsync(new[] { swarmB.AsPeer }, null);
                await swarmB.AddPeersAsync(new[] { swarmC.AsPeer }, null);

                swarmA.BroadcastTxs(new[] { tx3, tx4 });
                await swarmC.TxReceived.WaitAsync();
                Assert.DoesNotContain(tx3.Id, chainB.GetStagedTransactionIds());
                // SwarmC can not receive tx3 because SwarmB does not rebroadcast it.
                Assert.DoesNotContain(tx3.Id, chainC.GetStagedTransactionIds());
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
                await StopAsync(swarmC);

                swarmA.Dispose();
                swarmB.Dispose();
                swarmC.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task CanBroadcastBlock()
        {
            // If the bucket stored peers are the same, the block may not propagate,
            // so specify private keys to make the buckets different.
            var keyA = ByteUtil.ParseHex(
                "8568eb6f287afedece2c7b918471183db0451e1a61535bb0381cfdf95b85df20");
            var keyB = ByteUtil.ParseHex(
                "c34f7498befcc39a14f03b37833f6c7bb78310f1243616524eda70e078b8313c");
            var keyC = ByteUtil.ParseHex(
                "941bc2edfab840d79914d80fe3b30840628ac37a5d812d7f922b5d2405a223d3");

            var swarmA = CreateSwarm(new PrivateKey(keyA));
            var swarmB = CreateSwarm(new PrivateKey(keyB));
            var swarmC = CreateSwarm(new PrivateKey(keyC));

            BlockChain<DumbAction> chainA = swarmA.BlockChain;
            BlockChain<DumbAction> chainB = swarmB.BlockChain;
            BlockChain<DumbAction> chainC = swarmC.BlockChain;

            foreach (int i in Enumerable.Range(0, 10))
            {
                await chainA.MineBlock(swarmA.Address);
            }

            foreach (int i in Enumerable.Range(0, 3))
            {
                await chainB.MineBlock(swarmB.Address);
            }

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await StartAsync(swarmC);

                await BootstrapAsync(swarmB, swarmA.AsPeer);
                await BootstrapAsync(swarmC, swarmA.AsPeer);

                swarmB.BroadcastBlock(chainB[-1]);

                // chainA ignores block header received because its index is shorter.
                await swarmA.BlockHeaderReceived.WaitAsync();
                await swarmC.BlockAppended.WaitAsync();
                Assert.False(swarmA.BlockAppended.IsSet);

                // chainB doesn't applied to chainA since chainB is shorter
                // than chainA
                Assert.NotEqual(chainB, chainA);

                swarmA.BroadcastBlock(chainA[-1]);

                await swarmB.BlockAppended.WaitAsync();
                await swarmC.BlockAppended.WaitAsync();

                Log.Debug("Compare chainA and chainB");
                Assert.Equal(chainA.BlockHashes, chainB.BlockHashes);
                Log.Debug("Compare chainA and chainC");
                Assert.Equal(chainA.BlockHashes, chainC.BlockHashes);
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
                await StopAsync(swarmC);

                swarmA.Dispose();
                swarmB.Dispose();
                swarmC.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BroadcastBlockWithSkip()
        {
            var policy = new BlockPolicy<DumbAction>(new MinerReward(1));
            var fx1 = new DefaultStoreFixture(memory: true);
            var blockChain = TestUtils.MakeBlockChain(policy, fx1.Store, fx1.StateStore);
            var privateKey = new PrivateKey();
            var minerSwarm = CreateSwarm(blockChain, privateKey);
            var fx2 = new DefaultStoreFixture(memory: true);
            var receiverRenderer = new RecordingActionRenderer<DumbAction>();
            var loggedRenderer = new LoggedActionRenderer<DumbAction>(
                receiverRenderer,
                _logger);
            var receiverChain = TestUtils.MakeBlockChain(
                policy,
                fx2.Store,
                fx2.StateStore,
                renderers: new[] { loggedRenderer });
            Swarm<DumbAction> receiverSwarm = CreateSwarm(receiverChain);

            int renderCount = 0;

            receiverRenderer.RenderEventHandler += (_, a) => renderCount += a is DumbAction ? 1 : 0;

            Transaction<DumbAction>[] transactions =
            {
                fx1.MakeTransaction(
                    new[]
                    {
                        new DumbAction(fx1.Address2, "foo"),
                        new DumbAction(fx1.Address2, "bar"),
                    },
                    timestamp: DateTimeOffset.MinValue,
                    nonce: 0,
                    privateKey: privateKey),
                fx1.MakeTransaction(
                    new[]
                    {
                        new DumbAction(fx1.Address2, "baz"),
                        new DumbAction(fx1.Address2, "qux"),
                    },
                    timestamp: DateTimeOffset.MinValue.AddSeconds(5),
                    nonce: 1,
                    privateKey: privateKey),
            };

            try
            {
                await StartAsync(minerSwarm);
                await StartAsync(receiverSwarm);

                await BootstrapAsync(receiverSwarm, minerSwarm.AsPeer);

                var block1 = TestUtils.MineNext(
                        blockChain.Genesis,
                        policy.GetHashAlgorithm,
                        new[] { transactions[0] },
                        null,
                        policy.GetNextBlockDifficulty(blockChain))
                    .AttachStateRootHash(blockChain.StateStore, policy);
                blockChain.Append(block1, DateTimeOffset.MinValue.AddSeconds(3), true, true, false);
                var block2 = TestUtils.MineNext(
                    block1,
                    policy.GetHashAlgorithm,
                    new[] { transactions[1] },
                    null,
                    policy.GetNextBlockDifficulty(blockChain)
                ).AttachStateRootHash(blockChain.StateStore, policy);
                blockChain.Append(block2, DateTimeOffset.MinValue.AddSeconds(8), true, true, false);
                Log.Debug("Ready to broadcast blocks.");
                minerSwarm.BroadcastBlock(block2);
                await receiverSwarm.BlockAppended.WaitAsync();

                Assert.Equal(3, receiverChain.Count);
                Assert.Equal(4, renderCount);
            }
            finally
            {
                await StopAsync(minerSwarm);
                await StopAsync(receiverSwarm);
                fx1.Dispose();
                minerSwarm.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BroadcastBlockWithoutGenesis()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();

            BlockChain<DumbAction> chainA = swarmA.BlockChain;
            BlockChain<DumbAction> chainB = swarmB.BlockChain;

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);

                await BootstrapAsync(swarmB, swarmA.AsPeer);

                await chainA.MineBlock(swarmA.Address);
                swarmA.BroadcastBlock(chainA[-1]);

                await swarmB.BlockAppended.WaitAsync();

                Assert.Equal(chainB.BlockHashes, chainA.BlockHashes);

                await chainA.MineBlock(swarmA.Address);
                swarmA.BroadcastBlock(chainA[-1]);

                await swarmB.BlockAppended.WaitAsync();

                Assert.Equal(chainB.BlockHashes, chainA.BlockHashes);
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task IgnoreExistingBlocks()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();

            BlockChain<DumbAction> chainA = swarmA.BlockChain;
            BlockChain<DumbAction> chainB = swarmB.BlockChain;

            Block<DumbAction> genesis = await chainA.MineBlock(swarmA.Address);
            chainB.Append(genesis);

            foreach (int i in Enumerable.Range(0, 3))
            {
                await chainA.MineBlock(swarmA.Address);
            }

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);

                await BootstrapAsync(swarmB, swarmA.AsPeer);
                swarmA.BroadcastBlock(chainA[-1]);
                await swarmB.BlockAppended.WaitAsync();

                Assert.Equal(chainA.BlockHashes, chainB.BlockHashes);

                CancellationTokenSource cts = new CancellationTokenSource();
                swarmA.BroadcastBlock(chainA[-1]);
                Task t = swarmB.BlockAppended.WaitAsync(cts.Token);

                // Actually, previous code may pass this test if message is
                // delayed over 5 seconds.
                await Task.Delay(5000);
                Assert.False(t.IsCompleted);

                cts.Cancel();
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
            }
        }
    }
}
