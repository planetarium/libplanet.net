using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Security.Cryptography;
using System.Threading;
using System.Threading.Tasks;
using Bencodex.Types;
using Libplanet.Action;
using Libplanet.Blockchain;
using Libplanet.Blockchain.Policies;
using Libplanet.Blockchain.Renderers.Debug;
using Libplanet.Blocks;
using Libplanet.Crypto;
using Libplanet.Net;
using Libplanet.Net.Messages;
using Libplanet.Net.Protocols;
using Libplanet.Net.Transports;
using Libplanet.Store;
using Libplanet.Stun;
using Libplanet.Tests.Blockchain;
using Libplanet.Tests.Common.Action;
using Libplanet.Tests.Store;
using Libplanet.Tests.Store.Trie;
using Libplanet.Tx;
using NetMQ;
using NetMQ.Sockets;
using Serilog;
using xRetry;
using Xunit;
using Xunit.Abstractions;

namespace Libplanet.Tests.Net
{
    public partial class SwarmTest : IDisposable
    {
        private const int Timeout = 60 * 1000;
        private const int DisposeTimeout = 5 * 1000;

        private readonly ITestOutputHelper _output;
        private readonly ILogger _logger;

        public SwarmTest(ITestOutputHelper output)
        {
            const string outputTemplate =
                "{Timestamp:HH:mm:ss:ffffffZ}[@{SwarmId}][{ThreadId}] - {Message}";
            Log.Logger = new LoggerConfiguration()
                .MinimumLevel.Verbose()
                .Enrich.WithThreadId()
                .WriteTo.TestOutput(output, outputTemplate: outputTemplate)
                .CreateLogger()
                .ForContext<SwarmTest>();

            _logger = Log.ForContext<SwarmTest>();
            _output = output;

            _finalizers = new List<Func<Task>>();
        }

        public void Dispose()
        {
            Log.Logger.Debug("Starts to finalize {Resources} resources...", _finalizers.Count);
            int i = 1;
            foreach (Func<Task> finalize in _finalizers)
            {
                Log.Logger.Debug("Tries to finalize the resource #{Resource}...", i++);
                finalize().Wait(DisposeTimeout);
            }

            Log.Logger.Debug("Finished to finalize {Resources} resources.", _finalizers.Count);

            NetMQConfig.Cleanup(false);
            Log.Logger.Debug($"Finished to clean up the {nameof(NetMQConfig)} singleton.");
        }

        [Fact(Timeout = Timeout)]
        public async Task CanNotStartTwice()
        {
            Swarm<DumbAction> swarm = CreateSwarm();

            Task t = await Task.WhenAny(
                swarm.StartAsync(),
                swarm.StartAsync());

            Assert.True(swarm.Running);
            Assert.True(t.IsFaulted);
            Assert.True(
                t.Exception.InnerException is SwarmException,
                $"Expected SwarmException, but actual exception was: {t.Exception.InnerException}"
            );

            await StopAsync(swarm);
        }

        [Fact(Timeout = Timeout)]
        public async Task HandleReconnection()
        {
            Swarm<DumbAction> seed = CreateSwarm();

            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();

            try
            {
                await StartAsync(seed);
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await swarmA.AddPeersAsync(new[] { seed.AsPeer }, null);
                await StopAsync(swarmA);
                await swarmB.AddPeersAsync(new[] { seed.AsPeer }, null);

                Assert.Contains(swarmB.AsPeer, seed.Peers);
                Assert.Contains(seed.AsPeer, swarmB.Peers);
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
        public async Task StopAsyncTest()
        {
            Swarm<DumbAction> swarm = CreateSwarm();

            await swarm.StopAsync();
            var task = await StartAsync(swarm);

            Assert.True(swarm.Running);
            await swarm.StopAsync();

            Assert.False(swarm.Running);

            Assert.False(
                task.IsFaulted,
                $"A task was faulted due to an exception: {task.Exception}"
            );
        }

        [Fact(Timeout = Timeout)]
        public async Task CanWaitForRunning()
        {
            Swarm<DumbAction> swarm = CreateSwarm();

            Assert.False(swarm.Running);

            Task consumerTask = Task.Run(
                async () =>
                {
                    await swarm.WaitForRunningAsync();
                    Assert.True(swarm.Running);
                }
            );

            Task producerTask = Task.Run(async () => { await swarm.StartAsync(); });

            await consumerTask;
            Assert.True(swarm.Running);

            await StopAsync(swarm);
            Assert.False(swarm.Running);
        }

        [Fact(Timeout = Timeout)]
        public async Task AddPeersWithoutStart()
        {
            Swarm<DumbAction> a = CreateSwarm();
            Swarm<DumbAction> b = CreateSwarm();

            try
            {
                await StartAsync(b);

                await a.AddPeersAsync(new Peer[] { b.AsPeer }, null);

                Assert.Contains(b.AsPeer, a.Peers);
                Assert.Empty(b.Peers);
            }
            finally
            {
                await StopAsync(a);
                await StopAsync(b);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task AddPeersAsync()
        {
            Swarm<DumbAction> a = CreateSwarm();
            Swarm<DumbAction> b = CreateSwarm();

            try
            {
                await StartAsync(a);
                await StartAsync(b);

                await a.AddPeersAsync(new Peer[] { b.AsPeer }, null);

                Assert.Contains(a.AsPeer, b.Peers);
                Assert.Contains(b.AsPeer, a.Peers);
            }
            finally
            {
                await StopAsync(a);
                await StopAsync(b);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BootstrapException()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();

            try
            {
                await Assert.ThrowsAsync<PeerDiscoveryException>(
                    () => swarmB.BootstrapAsync(new[] { swarmA.AsPeer }, 3000, 3000));

                await StartAsync(swarmA);
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BootstrapAsyncWithoutStart()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();
            Swarm<DumbAction> swarmC = CreateSwarm();
            Swarm<DumbAction> swarmD = CreateSwarm();

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await StartAsync(swarmD);

                var bootstrappedAt = DateTimeOffset.UtcNow;
                swarmC.RoutingTable.AddPeer((BoundPeer)swarmD.AsPeer);
                await BootstrapAsync(swarmB, swarmA.AsPeer);
                await BootstrapAsync(swarmC, swarmA.AsPeer);

                Assert.Contains(swarmB.AsPeer, swarmC.Peers);
                Assert.DoesNotContain(swarmC.AsPeer, swarmB.Peers);
                foreach (PeerState state in swarmB.PeersStates)
                {
                    Assert.InRange(state.LastUpdated, bootstrappedAt, DateTimeOffset.UtcNow);
                }

                foreach (PeerState state in swarmC.PeersStates)
                {
                    if (state.Peer.Address == swarmD.AsPeer.Address)
                    {
                        // Peers added before bootstrap should not be marked as stale.
                        Assert.InRange(state.LastUpdated, bootstrappedAt, DateTimeOffset.UtcNow);
                    }
                    else
                    {
                        Assert.Equal(DateTimeOffset.MinValue, state.LastUpdated);
                    }
                }
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
                await StopAsync(swarmC);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task MaintainStaticPeers()
        {
            var keyA = new PrivateKey();
            Swarm<DumbAction> swarmA = CreateSwarm(keyA, listenPort: 20000);
            Swarm<DumbAction> swarmB = CreateSwarm(listenPort: 20001);
            Swarm<DumbAction> swarmC = CreateSwarm(keyA, listenPort: 20000);

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);

                Swarm<DumbAction> swarm = CreateSwarm(
                    options: new SwarmOptions
                    {
                        StaticPeers = new[]
                        {
                            (BoundPeer)swarmA.AsPeer,
                            (BoundPeer)swarmB.AsPeer,
                        }.ToImmutableHashSet(),
                        StaticPeersMaintainPeriod = TimeSpan.FromMilliseconds(100),
                    });

                await StartAsync(swarm);
                await Task.Delay(500);
                Assert.Contains(swarmA.AsPeer, swarm.Peers);
                Assert.Contains(swarmB.AsPeer, swarm.Peers);

                _logger.Debug("Address of swarmA: {Address}", swarmA.Address);
                await StopAsync(swarmA);
                await Task.Delay(100);
                await swarm.PeerDiscovery.RefreshTableAsync(
                    TimeSpan.Zero,
                    default(CancellationToken));
                // Invoke once more in case of swarmA and swarmB is in the same bucket,
                // and swarmA is last updated.
                await swarm.PeerDiscovery.RefreshTableAsync(
                    TimeSpan.Zero,
                    default(CancellationToken));
                Assert.DoesNotContain(swarmA.AsPeer, swarm.Peers);
                Assert.Contains(swarmB.AsPeer, swarm.Peers);

                await StartAsync(swarmC);
                await Task.Delay(500);
                Assert.Contains(swarmC.AsPeer, swarm.Peers);
                Assert.Contains(swarmB.AsPeer, swarm.Peers);

                await StopAsync(swarm);
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
                await StopAsync(swarmC);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task Cancel()
        {
            Swarm<DumbAction> swarm = CreateSwarm();
            var cts = new CancellationTokenSource();

            Task task = await StartAsync(
                swarm,
                cancellationToken: cts.Token
            );

            cts.Cancel();
            bool canceled = false;
            try
            {
                await task;
            }
            catch (OperationCanceledException)
            {
                canceled = true;
            }

            Assert.True(canceled);
        }

        [Fact(Timeout = Timeout)]
        public async Task GetBlocks()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();

            BlockChain<DumbAction> chainA = swarmA.BlockChain;
            BlockChain<DumbAction> chainB = swarmB.BlockChain;

            // FIXME: Rename the following variables or reuse the real genesis block which
            // already exists in chainA.  These are misleading as genesis.Index is not 0 but 1.
            Block<DumbAction> genesis = await chainA.MineBlock(swarmA.Address);
            chainB.Append(genesis); // chainA and chainB shares genesis block.
            Block<DumbAction> block1 = await chainA.MineBlock(swarmA.Address);
            Block<DumbAction> block2 = await chainA.MineBlock(swarmA.Address);

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);

                await swarmA.AddPeersAsync(new[] { swarmB.AsPeer }, null);

                (long, BlockHash)[] inventories1 = (
                    await swarmB.GetBlockHashes(
                        swarmA.AsPeer as BoundPeer,
                        new BlockLocator(new[] { genesis.Hash }),
                        null
                    ).ToArrayAsync()
                ).Select(p => p.ToValueTuple()).ToArray();
                Assert.Equal(
                    new[]
                    {
                        (genesis.Index, genesis.Hash),
                        (block1.Index, block1.Hash),
                        (block2.Index, block2.Hash),
                    },
                    inventories1);

                (long, BlockHash)[] inventories2 = (
                    await swarmB.GetBlockHashes(
                        swarmA.AsPeer as BoundPeer,
                        new BlockLocator(new[] { genesis.Hash }),
                        block1.Hash
                    ).ToArrayAsync()
                ).Select(p => p.ToValueTuple()).ToArray();
                Assert.Equal(
                    new[] { (genesis.Index, genesis.Hash), (block1.Index, block1.Hash) },
                    inventories2);

                Block<DumbAction>[] receivedBlocks =
                    await swarmB.GetBlocksAsync(
                        swarmA.AsPeer as BoundPeer,
                        inventories1.Select(pair => pair.Item2),
                        cancellationToken: default
                    ).ToArrayAsync();
                Assert.Equal(new[] { genesis, block1, block2 }, receivedBlocks);
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task GetMultipleBlocksAtOnce()
        {
            var privateKey = new PrivateKey();

            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm(privateKey);

            BlockChain<DumbAction> chainA = swarmA.BlockChain;
            BlockChain<DumbAction> chainB = swarmB.BlockChain;

            Block<DumbAction> genesis = await chainA.MineBlock(swarmA.Address);
            chainB.Append(genesis); // chainA and chainB shares genesis block.
            await chainA.MineBlock(swarmA.Address);
            await chainA.MineBlock(swarmA.Address);

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);

                var peer = swarmA.AsPeer as BoundPeer;

                await swarmB.AddPeersAsync(new[] { peer }, null);

                Tuple<long, BlockHash>[] hashes = await swarmB.GetBlockHashes(
                    peer,
                    new BlockLocator(new[] { genesis.Hash }),
                    null
                ).ToArrayAsync();

                var netMQAddress = $"tcp://{peer.EndPoint.Host}:{peer.EndPoint.Port}";
                using (var socket = new DealerSocket(netMQAddress))
                {
                    var request = new GetBlocks(hashes.Select(pair => pair.Item2), 2);
                    socket.SendMultipartMessage(
                        request.ToNetMQMessage(
                            privateKey,
                            swarmB.AsPeer,
                            DateTimeOffset.UtcNow,
                            swarmB.AppProtocolVersion)
                    );

                    NetMQMessage response = socket.ReceiveMultipartMessage();
                    Message parsedMessage = Message.Parse(
                        response,
                        true,
                        swarmA.AppProtocolVersion,
                        swarmA.TrustedAppProtocolVersionSigners,
                        null,
                        null);
                    Libplanet.Net.Messages.Blocks blockMessage =
                        (Libplanet.Net.Messages.Blocks)parsedMessage;

                    Assert.Equal(2, blockMessage.Payloads.Count);

                    response = socket.ReceiveMultipartMessage();
                    parsedMessage = Message.Parse(
                        response,
                        true,
                        swarmA.AppProtocolVersion,
                        swarmA.TrustedAppProtocolVersionSigners,
                        null,
                        null);
                    blockMessage = (Libplanet.Net.Messages.Blocks)parsedMessage;

                    Assert.Single(blockMessage.Payloads);
                }
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);

                swarmB.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task GetTx()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();

            BlockChain<DumbAction> chainB = swarmB.BlockChain;

            Transaction<DumbAction> tx = Transaction<DumbAction>.Create(
                0,
                new PrivateKey(),
                chainB.Genesis.Hash,
                new DumbAction[0]
            );
            chainB.StageTransaction(tx);
            await chainB.MineBlock(swarmB.Address);

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);

                await swarmA.AddPeersAsync(new[] { swarmB.AsPeer }, null);

                List<Transaction<DumbAction>> txs =
                    await swarmA.GetTxsAsync(
                        swarmB.AsPeer as BoundPeer,
                        new[] { tx.Id },
                        cancellationToken: default
                    ).ToListAsync();

                Assert.Equal(new[] { tx }, txs);
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
            }
        }

        [Fact(Timeout = Timeout)]
        public void ThrowArgumentExceptionInConstructor()
        {
            var fx = new DefaultStoreFixture();
            var policy = new BlockPolicy<DumbAction>();
            var blockchain = TestUtils.MakeBlockChain(policy, fx.Store, fx.StateStore);
            var key = new PrivateKey();
            AppProtocolVersion ver = AppProtocolVersion.Sign(key, 1);
            Assert.Throws<ArgumentNullException>(() => { new Swarm<DumbAction>(null, key, ver); });

            Assert.Throws<ArgumentNullException>(() =>
            {
                new Swarm<DumbAction>(blockchain, null, ver);
            });

            // Swarm<DumbAction> needs host or iceServers.
            Assert.Throws<ArgumentException>(() =>
            {
                new Swarm<DumbAction>(blockchain, key, ver);
            });

            // Swarm<DumbAction> needs host or iceServers.
            Assert.Throws<ArgumentException>(() =>
            {
                new Swarm<DumbAction>(blockchain, key, ver, iceServers: new IceServer[] { });
            });
        }

        [Fact(Timeout = Timeout)]
        public void CanResolveEndPoint()
        {
            var expected = new DnsEndPoint("1.2.3.4", 5678);
            using (Swarm<DumbAction> s = CreateSwarm(host: "1.2.3.4", listenPort: 5678))
            {
                Assert.Equal(expected, s.EndPoint);
                Assert.Equal(expected, (s.AsPeer as BoundPeer)?.EndPoint);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task StopGracefullyWhileStarting()
        {
            Swarm<DumbAction> a = CreateSwarm();

            Task t = await StartAsync(a);
            bool canceled = false;
            try
            {
                await Task.WhenAll(a.StopAsync(), t);
            }
            catch (OperationCanceledException)
            {
                canceled = true;
            }

            Assert.True(canceled || t.IsCompleted);
        }

        [Fact(Timeout = Timeout)]
        public async Task AsPeer()
        {
            Swarm<DumbAction> swarm = CreateSwarm();
            Assert.IsNotType<BoundPeer>(swarm.AsPeer);

            await StartAsync(swarm);
            Assert.IsType<BoundPeer>(swarm.AsPeer);
            await StopAsync(swarm);
        }

        [FactOnlyTurnAvailable(Timeout = Timeout)]
        public async Task ExchangeWithIceServer()
        {
            var iceServers = FactOnlyTurnAvailableAttribute.GetIceServers();
            var seed = CreateSwarm(host: "localhost");
            var swarmA = CreateSwarm(iceServers: iceServers);
            var swarmB = CreateSwarm(iceServers: iceServers);

            try
            {
                await StartAsync(seed);
                await StartAsync(swarmA);
                await StartAsync(swarmB);

                await swarmA.AddPeersAsync(new[] { seed.AsPeer }, null);
                await swarmB.AddPeersAsync(new[] { seed.AsPeer }, null);
                await swarmA.AddPeersAsync(new[] { swarmB.AsPeer }, null);

                Assert.Equal(
                    new HashSet<BoundPeer>
                    {
                        swarmA.AsPeer as BoundPeer,
                        swarmB.AsPeer as BoundPeer,
                    },
                    seed.Peers.ToHashSet());
                Assert.Equal(
                    new HashSet<BoundPeer> { seed.AsPeer as BoundPeer, swarmB.AsPeer as BoundPeer },
                    swarmA.Peers.ToHashSet());
                Assert.Equal(
                    new HashSet<BoundPeer> { seed.AsPeer as BoundPeer, swarmA.AsPeer as BoundPeer },
                    swarmB.Peers.ToHashSet());
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

        [FactOnlyTurnAvailable(10, 5000, Timeout = Timeout)]
        public async Task ReconnectToTurn()
        {
            int port;
            using (var socket = new Socket(SocketType.Stream, ProtocolType.Tcp))
            {
                socket.Bind(new IPEndPoint(IPAddress.Loopback, 0));
                port = ((IPEndPoint)socket.LocalEndPoint).Port;
            }

            Uri turnUrl = FactOnlyTurnAvailableAttribute.GetTurnUri();
            string[] userInfo = turnUrl.UserInfo.Split(':');
            string username = userInfo[0];
            string password = userInfo[1];
            var proxyUri = new Uri($"turn://{username}:{password}@localhost:{port}/");

            IEnumerable<IceServer> iceServers = new[]
            {
                new IceServer(urls: new[] { proxyUri }, username: username, credential: password),
            };

            var cts = new CancellationTokenSource();
            var proxyTask = TurnProxy(port, turnUrl, cts.Token);

            var seed = CreateSwarm(host: "localhost");
            var swarmA = CreateSwarm(iceServers: iceServers);

            async Task RefreshTableAsync(CancellationToken cancellationToken)
            {
                while (!cancellationToken.IsCancellationRequested)
                {
                    await Task.Delay(1000, cancellationToken);
                    try
                    {
                        await swarmA.PeerDiscovery.RefreshTableAsync(
                            TimeSpan.FromSeconds(1), cancellationToken);
                    }
                    catch (InvalidOperationException)
                    {
                    }
                    catch (TurnClientException)
                    {
                    }
                }
            }

            async Task MineAndBroadcast(CancellationToken cancellationToken)
            {
                while (!cancellationToken.IsCancellationRequested)
                {
                    var block = await seed.BlockChain.MineBlock(seed.Address);
                    seed.BroadcastBlock(block);
                    await Task.Delay(1000, cancellationToken);
                }
            }

            try
            {
                await StartAsync(seed);
                await StartAsync(swarmA);

                await swarmA.AddPeersAsync(new[] { seed.AsPeer }, null);

                cts.Cancel();
                await proxyTask;
                cts = new CancellationTokenSource();

                proxyTask = TurnProxy(port, turnUrl, cts.Token);
                _ = RefreshTableAsync(cts.Token);
                _ = MineAndBroadcast(cts.Token);

                await swarmA.BlockReceived.WaitAsync();
                cts.Cancel();
                await Task.Delay(1000);

                Assert.NotEqual(swarmA.BlockChain.Genesis, swarmA.BlockChain.Tip);
                Assert.Contains(
                    swarmA.BlockChain.Tip.Hash,
                    seed.BlockChain.BlockHashes
                );
            }
            finally
            {
                await StopAsync(seed);
                await StopAsync(swarmA);

                seed.Dispose();
                swarmA.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task RemoveForkedChainWhenFillBlocksAsyncFail()
        {
            // This test makes 2 different policies to reproduce an exception
            // while FillBlocksAsync.
            var policy1 = new BlockPolicy<DumbAction>();
            var policy2 = new NullPolicy<DumbAction>();
            var fx1 = new DefaultStoreFixture(true);
            var fx2 = new DefaultStoreFixture(true);

            var chain1 = TestUtils.MakeBlockChain(policy1, fx1.Store, fx1.StateStore);
            var chain2 = TestUtils.MakeBlockChain(policy2, fx2.Store, fx2.StateStore);

            var swarm1 = CreateSwarm(chain1);
            var swarm2 = CreateSwarm(chain2);

            Assert.Equal(chain1.Genesis, chain2.Genesis);

            await chain1.MineBlock(swarm1.Address);
            await chain2.MineBlock(swarm2.Address);

            // Creates a block that will make chain 2's total difficulty is higher than chain 1's.
            var block3 = TestUtils.MineNext(
                chain2.Tip,
                policy2.GetHashAlgorithm,
                difficulty: (long)chain1.Tip.TotalDifficulty + 1,
                blockInterval: TimeSpan.FromMilliseconds(1)
            ).AttachStateRootHash(chain2.StateStore, policy2);
            chain2.Append(block3);
            try
            {
                await StartAsync(swarm1);
                await StartAsync(swarm2);
                await swarm1.AddPeersAsync(new[] { swarm2.AsPeer }, null);

                swarm2.BroadcastBlock(block3);
                await swarm1.FillBlocksAsyncFailed.WaitAsync();

                List<Guid> chainIds = fx1.Store.ListChainIds().ToList();
                Assert.Single(chainIds);
            }
            finally
            {
                await StopAsync(swarm1);
                await StopAsync(swarm2);

                swarm1.Dispose();
                swarm2.Dispose();

                fx1.Dispose();
                fx2.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task RenderInFork()
        {
            var policy = new BlockPolicy<DumbAction>(new MinerReward(1));
            var renderer = new RecordingActionRenderer<DumbAction>();
            var chain = TestUtils.MakeBlockChain(
                policy,
                new DefaultStore(null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore()),
                renderers: new[] { renderer }
            );
            var miner1 = CreateSwarm(chain);
            var miner2 = CreateSwarm(TestUtils.MakeBlockChain(
                policy,
                new DefaultStore(null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore())));

            int renderCount = 0;

            var privKey = new PrivateKey();
            var addr = miner1.Address;
            var item = "foo";

            miner1.BlockChain.MakeTransaction(privKey, new[] { new DumbAction(addr, item) });
            await miner1.BlockChain.MineBlock(miner1.Address);

            miner2.BlockChain.MakeTransaction(privKey, new[] { new DumbAction(addr, item) });
            await miner2.BlockChain.MineBlock(miner2.Address);

            miner2.BlockChain.MakeTransaction(privKey, new[] { new DumbAction(addr, item) });
            var latest = await miner2.BlockChain.MineBlock(miner2.Address);

            renderer.RenderEventHandler += (_, a) =>
                renderCount += a is DumbAction ? 1 : 0;

            await StartAsync(miner1);
            await StartAsync(miner2);

            await BootstrapAsync(miner2, miner1.AsPeer);

            miner2.BroadcastBlock(latest);

            await miner1.BlockReceived.WaitAsync();

            Assert.Equal(miner1.BlockChain.Tip, miner2.BlockChain.Tip);
            Assert.Equal(miner1.BlockChain.Count, miner2.BlockChain.Count);
            Assert.Equal(2, renderCount);
        }

        [Fact(Timeout = Timeout)]
        public async Task ForkByDifficulty()
        {
            var policy = new BlockPolicy<DumbAction>(new MinerReward(1));
            var chain1 = TestUtils.MakeBlockChain(
                policy,
                new DefaultStore(null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore()));
            var chain2 = TestUtils.MakeBlockChain(
                policy,
                new DefaultStore(null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore()));

            var miner1 = CreateSwarm(chain1);
            var miner2 = CreateSwarm(chain2);

            await chain1.MineBlock(miner1.Address);
            await chain1.MineBlock(miner2.Address);
            long nextDifficulty =
                (long)chain1.Tip.TotalDifficulty + policy.GetNextBlockDifficulty(chain2);
            var block = TestUtils.MineNext(
                chain2.Tip,
                policy.GetHashAlgorithm,
                difficulty: nextDifficulty,
                blockInterval: TimeSpan.FromMilliseconds(1)
            ).AttachStateRootHash(chain2.StateStore, policy);
            chain2.Append(block);

            Assert.True(chain1.Tip.Index > chain2.Tip.Index);
            Assert.True(chain1.Tip.TotalDifficulty < chain2.Tip.TotalDifficulty);

            try
            {
                await StartAsync(miner1);
                await StartAsync(miner2);

                await BootstrapAsync(miner2, miner1.AsPeer);

                miner2.BroadcastBlock(block);
                await miner1.BlockReceived.WaitAsync();

                Assert.Equal(miner1.BlockChain.Tip, miner2.BlockChain.Tip);
                Assert.Equal(miner1.BlockChain.Count, miner2.BlockChain.Count);
            }
            finally
            {
                await StopAsync(miner1);
                await StopAsync(miner2);
                miner1.Dispose();
                miner2.Dispose();
            }
        }

        [Fact(Skip = "This should be fixed to work deterministically.")]
        public async Task HandleReorgInSynchronizing()
        {
            var policy = new BlockPolicy<Sleep>(new MinerReward(1));

            Swarm<Sleep> MakeSwarm() => CreateSwarm(TestUtils.MakeBlockChain(
                policy,
                new DefaultStore(null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore())));

            var miner1 = MakeSwarm();
            var miner2 = MakeSwarm();
            var receiver = MakeSwarm();

            foreach (var i in Enumerable.Range(0, 8))
            {
                miner1.BlockChain.StageTransaction(
                    Transaction<Sleep>.Create(
                        0,
                        new PrivateKey(),
                        miner1.BlockChain.Genesis.Hash,
                        actions: new[] { new Sleep() }
                    )
                );
                var b = await miner1.BlockChain.MineBlock(miner1.Address);
                miner2.BlockChain.Append(b);
            }

            try
            {
                await StartAsync(miner1);
                await StartAsync(miner2);

                await BootstrapAsync(miner2, miner1.AsPeer);
                await BootstrapAsync(receiver, miner1.AsPeer);

                var t = receiver.PreloadAsync();
                await miner1.BlockChain.MineBlock(miner1.Address);
                await miner2.BlockChain.MineBlock(miner2.Address);
                Block<Sleep> latest = await miner2.BlockChain.MineBlock(miner2.Address);
                miner2.BroadcastBlock(latest);
                await t;

                Assert.Equal(miner1.BlockChain.Tip, miner2.BlockChain.Tip);
                Assert.Equal(miner1.BlockChain.Count, miner2.BlockChain.Count);
                Assert.Equal(miner1.BlockChain.Count, receiver.BlockChain.Count);
                Assert.Equal(miner1.BlockChain.Tip, receiver.BlockChain.Tip);
            }
            finally
            {
                await StopAsync(miner1);
                await StopAsync(miner2);
                miner1.Dispose();
                miner2.Dispose();
                receiver.Dispose();
            }
        }

        [Theory(Timeout = Timeout)]
        [InlineData(true)]
        [InlineData(false)]
        public async void RestageTransactionsOnceLocallyMinedAfterReorg(bool restage)
        {
            var minerA = CreateSwarm();
            var minerB = CreateSwarm();

            var privateKeyA = new PrivateKey();
            var privateKeyB = new PrivateKey();

            var targetAddress1 = new PrivateKey().ToAddress();
            var targetAddress2 = new PrivateKey().ToAddress();

            try
            {
                const string dumbItem = "item0.0";
                var txA = minerA.BlockChain.MakeTransaction(
                    privateKeyA,
                    new[] { new DumbAction(targetAddress1, dumbItem), });
                var txB = minerB.BlockChain.MakeTransaction(
                    privateKeyB,
                    new[] { new DumbAction(targetAddress2, dumbItem), });

                if (!restage)
                {
                    minerB.BlockChain.StageTransaction(txA);
                }

                Log.Debug("Make minerB's chain longer than minerA's chain.");
                Block<DumbAction> blockA = await minerA.BlockChain.MineBlock(minerA.Address);
                Block<DumbAction> blockB = await minerB.BlockChain.MineBlock(minerB.Address);
                Block<DumbAction> blockC = await minerB.BlockChain.MineBlock(minerB.Address);

                Assert.Equal((Text)dumbItem, minerA.BlockChain.GetState(targetAddress1));
                Assert.Equal((Text)dumbItem, minerB.BlockChain.GetState(targetAddress2));

                await StartAsync(minerA);
                await StartAsync(minerB);

                await BootstrapAsync(minerA, minerB.AsPeer);

                Log.Debug("Reorg occurrs.");
                minerB.BroadcastBlock(blockC);
                await minerA.BlockAppended.WaitAsync();

                Assert.Equal(minerA.BlockChain.Tip, minerB.BlockChain.Tip);
                Assert.Equal(3, minerA.BlockChain.Count);
                Assert.Equal(
                    restage ? null : (Text?)dumbItem,
                    minerA.BlockChain.GetState(targetAddress1));
                Assert.Equal((Text)dumbItem, minerA.BlockChain.GetState(targetAddress2));

                Log.Debug("Check if txs in unrendered blocks staged again.");
                Assert.Equal(
                    restage,
                    minerA.BlockChain.GetStagedTransactionIds().Contains(txA.Id));

                await minerA.BlockChain.MineBlock(minerA.Address);
                minerA.BroadcastBlock(minerA.BlockChain.Tip);
                await minerB.BlockAppended.WaitAsync();

                Assert.Equal(minerA.BlockChain.Tip, minerB.BlockChain.Tip);
                Assert.Equal((Text)dumbItem, minerA.BlockChain.GetState(targetAddress1));
                Assert.Equal((Text)dumbItem, minerA.BlockChain.GetState(targetAddress2));
            }
            finally
            {
                await StopAsync(minerA);
                await StopAsync(minerB);

                minerA.Dispose();
                minerB.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task UnstageInvalidTransaction()
        {
            var validKey = new PrivateKey();

            bool IsSignerValid(Transaction<DumbAction> tx, BlockChain<DumbAction> chain)
            {
                var validAddress = validKey.PublicKey.ToAddress();
                return tx.Signer.Equals(validAddress);
            }

            var policy = new BlockPolicy<DumbAction>(doesTransactionFollowPolicy: IsSignerValid);
            var fx1 = new DefaultStoreFixture();
            var fx2 = new DefaultStoreFixture();

            var swarmA = CreateSwarm(
                TestUtils.MakeBlockChain(policy, fx1.Store, fx1.StateStore, privateKey: validKey));
            var swarmB = CreateSwarm(
                TestUtils.MakeBlockChain(policy, fx2.Store, fx2.StateStore, privateKey: validKey));

            var invalidKey = new PrivateKey();

            try
            {
                var validTx = swarmA.BlockChain.MakeTransaction(validKey, new DumbAction[] { });
                var invalidTx = swarmA.BlockChain.MakeTransaction(invalidKey, new DumbAction[] { });

                await StartAsync(swarmA);
                await StartAsync(swarmB);

                await BootstrapAsync(swarmA, swarmB.AsPeer);

                swarmA.BroadcastTxs(new[] { validTx, invalidTx });
                await swarmB.TxReceived.WaitAsync();

                Assert.Equal(swarmB.BlockChain.GetTransaction(validTx.Id), validTx);
                Assert.Throws<KeyNotFoundException>(
                    () => swarmB.BlockChain.GetTransaction(invalidTx.Id)
                );

                Assert.Contains(validTx.Id, swarmB.BlockChain.GetStagedTransactionIds());
                Assert.DoesNotContain(invalidTx.Id, swarmB.BlockChain.GetStagedTransactionIds());
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);

                swarmA.Dispose();
                swarmB.Dispose();

                fx1.Dispose();
                fx2.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task IgnoreTransactionFromDifferentGenesis()
        {
            var validKey = new PrivateKey();

            bool IsSignerValid(Transaction<DumbAction> tx, BlockChain<DumbAction> chain)
            {
                var validAddress = validKey.PublicKey.ToAddress();
                return tx.Signer.Equals(validAddress);
            }

            var policy = new BlockPolicy<DumbAction>(doesTransactionFollowPolicy: IsSignerValid);
            var fx1 = new DefaultStoreFixture();
            var fx2 = new DefaultStoreFixture();

            var swarmA = CreateSwarm(
                TestUtils.MakeBlockChain(
                    policy,
                    fx1.Store,
                    fx1.StateStore,
                    privateKey: validKey,
                    timestamp: DateTimeOffset.MinValue));
            var swarmB = CreateSwarm(
                TestUtils.MakeBlockChain(
                    policy,
                    fx2.Store,
                    fx2.StateStore,
                    privateKey: validKey,
                    timestamp: DateTimeOffset.MinValue.AddSeconds(1)));

            try
            {
                var tx = swarmA.BlockChain.MakeTransaction(validKey, new DumbAction[] { });

                await StartAsync(swarmA);
                await StartAsync(swarmB);

                await BootstrapAsync(swarmA, swarmB.AsPeer);

                swarmA.BroadcastTxs(new[] { tx });
                await swarmB.TxReceived.WaitAsync();

                Assert.Throws<KeyNotFoundException>(() => swarmB.BlockChain.GetTransaction(tx.Id));
                Assert.DoesNotContain(tx.Id, swarmB.BlockChain.GetStagedTransactionIds());
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);

                swarmA.Dispose();
                swarmB.Dispose();

                fx1.Dispose();
                fx2.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task CreateNewChainWhenBranchPointNotExist()
        {
            // If the bucket stored peers are the same, the block may not propagate,
            // so specify private keys to make the buckets different.
            var keyA = ByteUtil.ParseHex(
                "8568eb6f287afedece2c7b918471183db0451e1a61535bb0381cfdf95b85df20");
            var keyB = ByteUtil.ParseHex(
                "c34f7498befcc39a14f03b37833f6c7bb78310f1243616524eda70e078b8313c");
            var keyC = ByteUtil.ParseHex(
                "941bc2edfab840d79914d80fe3b30840628ac37a5d812d7f922b5d2405a223d3");

            var minerSwarmA = CreateSwarm(new PrivateKey(keyA));
            var minerSwarmB = CreateSwarm(new PrivateKey(keyB));
            var receiverSwarm = CreateSwarm(new PrivateKey(keyC));

            BlockChain<DumbAction> minerChainA = minerSwarmA.BlockChain;
            BlockChain<DumbAction> minerChainB = minerSwarmB.BlockChain;
            BlockChain<DumbAction> receiverChain = receiverSwarm.BlockChain;

            try
            {
                await StartAsync(minerSwarmA);
                await StartAsync(minerSwarmB);
                await StartAsync(receiverSwarm);

                await BootstrapAsync(minerSwarmA, receiverSwarm.AsPeer);
                await BootstrapAsync(minerSwarmB, receiverSwarm.AsPeer);

                // Broadcast SwarmA's first block.
                var b1 = await minerChainA.MineBlock(minerSwarmA.Address);
                await minerChainB.MineBlock(minerSwarmA.Address);
                minerSwarmA.BroadcastBlock(b1);
                await receiverSwarm.BlockAppended.WaitAsync();
                Assert.Equal(receiverChain.Tip, minerChainA.Tip);

                // Broadcast SwarmB's second block.
                await minerChainA.MineBlock(minerSwarmA.Address);
                var b2 = await minerChainB.MineBlock(minerSwarmA.Address);
                minerSwarmB.BroadcastBlock(b2);
                await receiverSwarm.BlockAppended.WaitAsync();
                Assert.Equal(receiverChain.Tip, minerChainB.Tip);

                // Broadcast SwarmA's third block.
                var b3 = await minerChainA.MineBlock(minerSwarmA.Address);
                await minerChainB.MineBlock(minerSwarmA.Address);
                minerSwarmA.BroadcastBlock(b3);
                await receiverSwarm.BlockAppended.WaitAsync();
                Assert.Equal(receiverChain.Tip, minerChainA.Tip);
            }
            finally
            {
                await StopAsync(minerSwarmA);
                await StopAsync(minerSwarmB);
                await StopAsync(receiverSwarm);
                minerSwarmA.Dispose();
                minerSwarmB.Dispose();
                receiverSwarm.Dispose();
            }
        }

        [RetryFact(10, Timeout = Timeout)]
        public async Task DoNotDeleteCanonicalChainWhenBlockDownloadFailed()
        {
            var swarmA = CreateSwarm();
            var swarmB = CreateSwarm();
            var chainA = swarmA.BlockChain;
            var chainB = swarmB.BlockChain;

            swarmB.Options.BlockHashRecvTimeout = TimeSpan.FromMilliseconds(10);

            var genesis = await chainA.MineBlock(swarmA.Address);
            chainB.Append(genesis);

            await chainA.MineBlock(swarmA.Address);
            var block = await chainA.MineBlock(swarmA.Address);

            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await BootstrapAsync(swarmA, swarmB.AsPeer);

                Task task = swarmB.FillBlocksAsyncStarted.WaitAsync();
                swarmA.BroadcastBlock(block);
                await task;
                task = swarmB.FillBlocksAsyncFailed.WaitAsync();
                await StopAsync(swarmA);
                await task;

                Assert.NotNull(chainB.GetState(swarmA.Address));
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task DoNotReceiveBlockFromNodeHavingDifferenceGenesisBlock()
        {
            var keyA = ByteUtil.ParseHex(
                "8568eb6f287afedece2c7b918471183db0451e1a61535bb0381cfdf95b85df20");
            var keyB = ByteUtil.ParseHex(
                "c34f7498befcc39a14f03b37833f6c7bb78310f1243616524eda70e078b8313c");
            var keyC = ByteUtil.ParseHex(
                "941bc2edfab840d79914d80fe3b30840628ac37a5d812d7f922b5d2405a223d3");

            var privateKeyA = new PrivateKey(keyA);
            var privateKeyB = new PrivateKey(keyB);
            var privateKeyC = new PrivateKey(keyC);

            var signerAddress = new PrivateKey().ToAddress();

            var actionsA = new[] { new DumbAction(signerAddress, "1") };
            var actionsB = new[] { new DumbAction(signerAddress, "2") };

            HashAlgorithmType alg = HashAlgorithmType.Of<SHA256>();
            var genesisBlockA = BlockChain<DumbAction>.MakeGenesisBlock(alg, actionsA, privateKeyA);
            var genesisBlockB = BlockChain<DumbAction>.MakeGenesisBlock(alg, actionsB, privateKeyB);

            BlockChain<DumbAction> MakeGenesisChain(
                IStore store, IStateStore stateStore, Block<DumbAction> genesisBlock) =>
                new BlockChain<DumbAction>(
                    new BlockPolicy<DumbAction>(),
                    new VolatileStagePolicy<DumbAction>(),
                    store,
                    stateStore,
                    genesisBlock);

            var genesisChainA = MakeGenesisChain(
                new DefaultStore(null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore()),
                genesisBlockA);
            var genesisChainB = MakeGenesisChain(
                new DefaultStore(null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore()),
                genesisBlockB);
            var genesisChainC = MakeGenesisChain(
                new DefaultStore(null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore()),
                genesisBlockA);

            var swarmA = CreateSwarm(genesisChainA, privateKeyA);
            var swarmB = CreateSwarm(genesisChainB, privateKeyB);
            var swarmC = CreateSwarm(genesisChainC, privateKeyC);
            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await StartAsync(swarmC);

                await swarmB.AddPeersAsync(new[] { swarmA.AsPeer }, null);
                await swarmC.AddPeersAsync(new[] { swarmA.AsPeer }, null);

                var block = await swarmA.BlockChain.MineBlock(swarmA.Address);

                Task.WaitAll(new[]
                {
                    Task.Run(() => swarmC.BlockAppended.Wait()),
                    Task.Run(() => swarmA.BroadcastBlock(block)),
                });

                Assert.NotEqual(genesisChainA.Genesis, genesisChainB.Genesis);
                Assert.Equal(genesisChainA.BlockHashes, genesisChainC.BlockHashes);
                Assert.Equal(2, genesisChainA.Count);
                Assert.Equal(1, genesisChainB.Count);
                Assert.Equal(2, genesisChainC.Count);

                Assert.Equal("1", (Text)genesisChainA.GetState(signerAddress));
                Assert.Equal("2", (Text)genesisChainB.GetState(signerAddress));
                Assert.Equal("1", (Text)genesisChainC.GetState(signerAddress));
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
        public async Task FindSpecificPeerAsync()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();
            Swarm<DumbAction> swarmC = CreateSwarm();
            Swarm<DumbAction> swarmD = CreateSwarm();
            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await StartAsync(swarmC);
                await StartAsync(swarmD);

                await swarmA.AddPeersAsync(new Peer[] { swarmB.AsPeer }, null);
                await swarmB.AddPeersAsync(new Peer[] { swarmC.AsPeer }, null);
                await swarmC.AddPeersAsync(new Peer[] { swarmD.AsPeer }, null);

                BoundPeer foundPeer = await swarmA.FindSpecificPeerAsync(
                    swarmB.AsPeer.Address,
                    -1,
                    TimeSpan.FromMilliseconds(3000));

                Assert.Equal(swarmB.AsPeer.Address, foundPeer.Address);
                Assert.DoesNotContain(swarmC.AsPeer, swarmA.Peers);

                foundPeer = await swarmA.FindSpecificPeerAsync(
                    swarmD.AsPeer.Address,
                    -1,
                    TimeSpan.FromMilliseconds(3000));

                Assert.Equal(swarmD.AsPeer.Address, foundPeer.Address);
                Assert.Contains(swarmC.AsPeer, swarmA.Peers);
                Assert.Contains(swarmD.AsPeer, swarmA.Peers);
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
                await StopAsync(swarmC);
                await StopAsync(swarmD);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task FindSpecificPeerAsyncFail()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();
            Swarm<DumbAction> swarmC = CreateSwarm();
            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await StartAsync(swarmC);

                await swarmA.AddPeersAsync(new Peer[] { swarmB.AsPeer }, null);
                await swarmB.AddPeersAsync(new Peer[] { swarmC.AsPeer }, null);

                await StopAsync(swarmB);

                BoundPeer foundPeer = await swarmA.FindSpecificPeerAsync(
                    swarmB.AsPeer.Address,
                    -1,
                    TimeSpan.FromMilliseconds(3000));

                Assert.Null(foundPeer);

                foundPeer = await swarmA.FindSpecificPeerAsync(
                    swarmC.AsPeer.Address,
                    -1,
                    TimeSpan.FromMilliseconds(3000));

                Assert.Null(foundPeer);
                Assert.DoesNotContain(swarmC.AsPeer, swarmA.Peers);
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
                await StopAsync(swarmC);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task FindSpecificPeerAsyncDepthFail()
        {
            Swarm<DumbAction> swarmA = CreateSwarm();
            Swarm<DumbAction> swarmB = CreateSwarm();
            Swarm<DumbAction> swarmC = CreateSwarm();
            Swarm<DumbAction> swarmD = CreateSwarm();
            try
            {
                await StartAsync(swarmA);
                await StartAsync(swarmB);
                await StartAsync(swarmC);
                await StartAsync(swarmD);

                await swarmA.AddPeersAsync(new Peer[] { swarmB.AsPeer }, null);
                await swarmB.AddPeersAsync(new Peer[] { swarmC.AsPeer }, null);
                await swarmC.AddPeersAsync(new Peer[] { swarmD.AsPeer }, null);

                BoundPeer foundPeer = await swarmA.FindSpecificPeerAsync(
                    swarmC.AsPeer.Address,
                    1,
                    TimeSpan.FromMilliseconds(3000));

                Assert.Equal(swarmC.AsPeer.Address, foundPeer.Address);
                swarmA.RoutingTable.Clear();
                Assert.Empty(swarmA.Peers);
                await swarmA.AddPeersAsync(new Peer[] { swarmB.AsPeer }, null);

                foundPeer = await swarmA.FindSpecificPeerAsync(
                    swarmD.AsPeer.Address,
                    1,
                    TimeSpan.FromMilliseconds(3000));

                Assert.Null(foundPeer);
            }
            finally
            {
                await StopAsync(swarmA);
                await StopAsync(swarmB);
                await StopAsync(swarmC);
                await StopAsync(swarmD);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task DoNotFillWhenGetAllBlockAtFirstTimeFromSender()
        {
            Swarm<DumbAction> receiver = CreateSwarm();
            Swarm<DumbAction> sender = CreateSwarm();
            await StartAsync(receiver);
            await StartAsync(sender);

            receiver.FindNextHashesChunkSize = 8;
            sender.FindNextHashesChunkSize = 8;
            BlockChain<DumbAction> chain = sender.BlockChain;

            for (int i = 0; i < 6; i++)
            {
                Block<DumbAction> block =
                    TestUtils.MineNext(chain.Tip, chain.Policy.GetHashAlgorithm, difficulty: 1024)
                        .AttachStateRootHash(chain.StateStore, chain.Policy);
                chain.Append(block);
            }

            Log.Debug("Sender's BlockChain Tip index: #{index}", sender.BlockChain.Tip.Index);

            try
            {
                await BootstrapAsync(sender, receiver.AsPeer);

                sender.BroadcastBlock(sender.BlockChain.Tip);

                await receiver.BlockReceived.WaitAsync();
                Assert.Equal(
                    7,
                    receiver.BlockChain.Count);
            }
            finally
            {
                await StopAsync(receiver);
                await StopAsync(sender);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task FillWhenGetAllBlocksFromSender()
        {
            Swarm<DumbAction> receiver = CreateSwarm();
            Swarm<DumbAction> sender = CreateSwarm();
            await StartAsync(receiver);
            await StartAsync(sender);

            receiver.FindNextHashesChunkSize = 2;
            sender.FindNextHashesChunkSize = 2;
            BlockChain<DumbAction> chain = sender.BlockChain;

            for (int i = 0; i < 6; i++)
            {
                Block<DumbAction> block =
                    TestUtils.MineNext(chain.Tip, chain.Policy.GetHashAlgorithm, difficulty: 1024)
                        .AttachStateRootHash(chain.StateStore, chain.Policy);
                chain.Append(block);
            }

            Log.Debug("Sender's BlockChain Tip index: #{index}", sender.BlockChain.Tip.Index);

            try
            {
                await BootstrapAsync(sender, receiver.AsPeer);

                sender.BroadcastBlock(sender.BlockChain.Tip);

                await receiver.BlockReceived.WaitAsync();
                Assert.Equal(
                    7,
                    receiver.BlockChain.Count);
            }
            finally
            {
                await StopAsync(receiver);
                await StopAsync(sender);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task DoNotFillMultipleTimes()
        {
            Swarm<DumbAction> receiver = CreateSwarm();
            Swarm<DumbAction> sender1 = CreateSwarm();
            Swarm<DumbAction> sender2 = CreateSwarm();

            await StartAsync(receiver);
            await StartAsync(sender1);
            await StartAsync(sender2);

            BlockChain<DumbAction> chain = receiver.BlockChain;
            Block<DumbAction> b1 =
                TestUtils.MineNext(chain.Genesis, chain.Policy.GetHashAlgorithm, difficulty: 1024)
                    .AttachStateRootHash(sender1.BlockChain.StateStore, chain.Policy);

            try
            {
                await BootstrapAsync(sender1, receiver.AsPeer);
                await BootstrapAsync(sender2, receiver.AsPeer);

                sender1.BlockChain.Append(b1);
                sender2.BlockChain.Append(b1);

                sender1.BroadcastBlock(b1);
                sender2.BroadcastBlock(b1);

                // Make sure that receiver swarm only filled once for same block
                // that were broadcasted simultaneously.
                await receiver.BlockReceived.WaitAsync();

                // Awaits 1 second because receiver swarm may tried to fill again after filled.
                await Task.Delay(1000);
                var transport = receiver.Transport as NetMQTransport;
                Log.Debug("Messages: {@Message}", transport.MessageHistory);
                Assert.Single(
                    transport.MessageHistory.Where(msg => msg is Libplanet.Net.Messages.Blocks));

                Transaction<DumbAction> tx = Transaction<DumbAction>.Create(
                    0,
                    new PrivateKey(),
                    sender1.BlockChain.Genesis.Hash,
                    new DumbAction[] { }
                );
                sender1.BlockChain.StageTransaction(tx);
                sender2.BlockChain.StageTransaction(tx);

                // Make sure that receiver swarm only filled once for same transaction
                // that were broadcasted simultaneously.
                sender1.BroadcastTxs(new[] { tx });
                sender2.BroadcastTxs(new[] { tx });

                await receiver.TxReceived.WaitAsync();

                // Awaits 1 second because receiver swarm may tried to fill again after filled.
                await Task.Delay(1000);
                Assert.Single(
                    transport.MessageHistory.Where(msg => msg is Libplanet.Net.Messages.Tx));
            }
            finally
            {
                await StopAsync(receiver);
                await StopAsync(sender1);
                await StopAsync(sender2);
            }
        }

        [RetryFact(10, Timeout = Timeout)]
        public async Task GetPeerChainStateAsync()
        {
            Swarm<DumbAction> swarm1 = CreateSwarm();
            Swarm<DumbAction> swarm2 = CreateSwarm();
            Swarm<DumbAction> swarm3 = CreateSwarm();

            var peerChainState = await swarm1.GetPeerChainStateAsync(
                TimeSpan.FromSeconds(1), default);
            Assert.Empty(peerChainState);

            try
            {
                await StartAsync(swarm2);
                await StartAsync(swarm3);

                await BootstrapAsync(swarm1, swarm2.AsPeer);

                peerChainState = await swarm1.GetPeerChainStateAsync(
                    TimeSpan.FromSeconds(1), default);
                Assert.Equal(
                    new PeerChainState((BoundPeer)swarm2.AsPeer, 0, 0),
                    peerChainState.First()
                );

                await swarm2.BlockChain.MineBlock(swarm2.Address);
                peerChainState = await swarm1.GetPeerChainStateAsync(
                    TimeSpan.FromSeconds(1), default);
                Assert.Equal(
                    new PeerChainState((BoundPeer)swarm2.AsPeer, 1, 1024),
                    peerChainState.First()
                );

                await BootstrapAsync(swarm1, swarm3.AsPeer);
                peerChainState = await swarm1.GetPeerChainStateAsync(
                    TimeSpan.FromSeconds(1), default);
                Assert.Equal(
                    new[]
                    {
                        new PeerChainState((BoundPeer)swarm2.AsPeer, 1, 1024),
                        new PeerChainState((BoundPeer)swarm3.AsPeer, 0, 0),
                    }.ToHashSet(),
                    peerChainState.ToHashSet()
                );
            }
            finally
            {
                await StopAsync(swarm2);
                await StopAsync(swarm3);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task LastMessageTimestamp()
        {
            Swarm<DumbAction> swarm1 = CreateSwarm();
            Swarm<DumbAction> swarm2 = CreateSwarm();

            Assert.Null(swarm1.LastMessageTimestamp);

            try
            {
                await StartAsync(swarm1);
                Assert.Null(swarm1.LastMessageTimestamp);
                DateTimeOffset bootstrappedAt = DateTimeOffset.UtcNow;
                await BootstrapAsync(swarm2, swarm1.AsPeer);
                await StartAsync(swarm2);

                Assert.NotNull(swarm1.LastMessageTimestamp);
                Assert.InRange(
                    swarm1.LastMessageTimestamp.Value,
                    bootstrappedAt,
                    DateTimeOffset.UtcNow
                );
            }
            finally
            {
                await StopAsync(swarm1);
                await StopAsync(swarm2);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BlockDemand()
        {
            SwarmOptions swarmOptions = new SwarmOptions
            {
                // This value should be shorter than fillblock's timeout for testing.
                BlockDemandLifespan = TimeSpan.FromSeconds(3),
            };
            var minerKey = new PrivateKey();
            var policy = new BlockPolicy<DumbAction>(new MinerReward(1));
            Swarm<DumbAction> swarm = CreateSwarm(
                privateKey: new PrivateKey(),
                options: swarmOptions);
            var dummy = TestUtils.MakeBlockChain(
                policy,
                new DefaultStore(path: null),
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore()));
            for (var i = 0; i < 20; i++)
            {
                await dummy.MineBlock(minerKey.ToAddress());
            }

            try
            {
                await StartAsync(swarm);
                BoundPeer peer = swarm.AsPeer as BoundPeer;
                Assert.NotNull(peer);
                _logger.Debug(
                    "{0}///{1}///{2}",
                    peer.PublicKey,
                    peer.EndPoint,
                    peer.PublicIPAddress);

                Block<DumbAction> lowerBlock = dummy[10];
                Block<DumbAction> higherBlock = dummy[20];
                Assert.True(lowerBlock.TotalDifficulty < higherBlock.TotalDifficulty);
                var privateKey1 = new PrivateKey();
                var privateKey2 = new PrivateKey();
                var sender1 = new BoundPeer(
                    privateKey1.PublicKey,
                    new DnsEndPoint("127.0.0.1", 20000));
                var sender2 = new BoundPeer(
                    privateKey2.PublicKey,
                    new DnsEndPoint("127.0.0.1", 20001));
                _logger.Debug(
                    "{0}///{1}///{2}",
                    sender1.PublicKey,
                    sender1.EndPoint,
                    sender1.PublicIPAddress);
                _logger.Debug("STEP1");

                var netMQAddress = $"tcp://{peer.EndPoint.Host}:{peer.EndPoint.Port}";
                using (var socket = new DealerSocket(netMQAddress))
                {
                    var request =
                        new BlockHeaderMessage(swarm.BlockChain.Genesis.Hash, higherBlock.Header);
                    socket.SendMultipartMessage(
                        request.ToNetMQMessage(
                            privateKey1,
                            sender1,
                            DateTimeOffset.UtcNow,
                            swarm.AppProtocolVersion)
                    );
                    await swarm.BlockHeaderReceived.WaitAsync();
                    await Task.Delay(100);
                    Assert.NotNull(swarm.BlockDemand);
                    var timestamp = swarm.BlockDemand.Value.Timestamp;
                    Assert.Equal(higherBlock.Index, swarm.BlockDemand.Value.Header.Index);

                    request =
                        new BlockHeaderMessage(swarm.BlockChain.Genesis.Hash, lowerBlock.Header);
                    socket.SendMultipartMessage(
                        request.ToNetMQMessage(
                            privateKey2,
                            sender2,
                            DateTimeOffset.UtcNow,
                            swarm.AppProtocolVersion)
                    );
                    await swarm.BlockHeaderReceived.WaitAsync();
                    // Await for context change
                    await Task.Delay(100);
                    Assert.NotNull(swarm.BlockDemand);
                    // Demand will not be refreshed.
                    Assert.Equal(higherBlock.Index, swarm.BlockDemand.Value.Header.Index);
                    Assert.Equal(timestamp, swarm.BlockDemand.Value.Timestamp);

                    await Task.Delay(
                        swarmOptions.BlockDemandLifespan + TimeSpan.FromMilliseconds(100));

                    request =
                        new BlockHeaderMessage(swarm.BlockChain.Genesis.Hash, higherBlock.Header);
                    socket.SendMultipartMessage(
                        request.ToNetMQMessage(
                            privateKey1,
                            sender1,
                            DateTimeOffset.UtcNow,
                            swarm.AppProtocolVersion)
                    );
                    await swarm.BlockHeaderReceived.WaitAsync();
                    await Task.Delay(100);
                    Assert.NotNull(swarm.BlockDemand);
                    // Demand will not be refreshed.
                    Assert.Equal(higherBlock.Index, swarm.BlockDemand.Value.Header.Index);
                    Assert.Equal(timestamp, swarm.BlockDemand.Value.Timestamp);

                    request =
                        new BlockHeaderMessage(swarm.BlockChain.Genesis.Hash, lowerBlock.Header);
                    socket.SendMultipartMessage(
                        request.ToNetMQMessage(
                            privateKey2,
                            sender2,
                            DateTimeOffset.UtcNow,
                            swarm.AppProtocolVersion)
                    );
                    await swarm.BlockHeaderReceived.WaitAsync();
                    await Task.Delay(100);
                    _logger.Debug("STEP5");
                    Assert.NotNull(swarm.BlockDemand);
                    // Demand will be replaced to lower one because it's stale.
                    Assert.Equal(lowerBlock.Index, swarm.BlockDemand.Value.Header.Index);
                }
            }
            finally
            {
                await StopAsync(swarm);
            }
        }

        [Fact]
        public async Task ResetBlockDemandIfNotChanged()
        {
            var minerKey = new PrivateKey();
            Swarm<DumbAction> sender = CreateSwarm();
            Swarm<DumbAction> receiver = CreateSwarm();
            for (var i = 0; i < 20; i++)
            {
                await sender.BlockChain.MineBlock(minerKey.ToAddress());
            }

            Block<DumbAction> lowerBlock = sender.BlockChain[19],
                higherBlock = sender.BlockChain[20];

            await StartAsync(sender);
            await StartAsync(receiver);
            await BootstrapAsync(sender, receiver.AsPeer);

            sender.BroadcastBlock(lowerBlock);
            await receiver.FillBlocksAsyncStarted.WaitAsync();
            sender.BroadcastBlock(higherBlock);
            await receiver.ProcessFillBlocksFinished.WaitAsync();

            Assert.NotNull(receiver.BlockDemand);
            Assert.Equal(
                higherBlock.Hash,
                new BlockHash(receiver.BlockDemand.Value.Header.Hash));
        }

        private async Task<Task> StartAsync<T>(
            Swarm<T> swarm,
            CancellationToken cancellationToken = default
        )
            where T : IAction, new()
        {
            Task task = swarm.StartAsync(
                millisecondsDialTimeout: 200,
                millisecondsBroadcastBlockInterval: 15 * 1000,
                millisecondsBroadcastTxInterval: 200,
                cancellationToken: cancellationToken
            );
            await swarm.WaitForRunningAsync();
            return task;
        }

        private Task StopAsync<T>(Swarm<T> swarm)
            where T : IAction, new()
        {
            return swarm.StopAsync(TimeSpan.FromMilliseconds(10));
        }

        private Task BootstrapAsync<T>(
            Swarm<T> swarm,
            Peer seed,
            CancellationToken cancellationToken = default
        )
            where T : IAction, new() =>
            BootstrapAsync(swarm, new[] { seed }, cancellationToken);

        private async Task BootstrapAsync<T>(
            Swarm<T> swarm,
            IEnumerable<Peer> seeds,
            CancellationToken cancellationToken = default
        )
            where T : IAction, new()
        {
            await swarm.BootstrapAsync(
                seeds,
                null,
                findNeighborsTimeout: TimeSpan.FromSeconds(3),
                cancellationToken: cancellationToken);
        }

        private async Task TurnProxy(
            int port,
            Uri turnUri,
            CancellationToken cancellationToken)
        {
            var server = new TcpListener(IPAddress.Loopback, port);
            server.Start();
            var tasks = new List<Task>();
            var clients = new List<TcpClient>();

            cancellationToken.Register(() => server.Stop());
            while (!cancellationToken.IsCancellationRequested)
            {
                TcpClient client;
                try
                {
                    client = await server.AcceptTcpClientAsync();
                }
                catch (ObjectDisposedException)
                {
                    break;
                }

                clients.Add(client);

                tasks.Add(Task.Run(
                    async () =>
                    {
                        const int bufferSize = 8192;
                        NetworkStream stream = client.GetStream();

                        using (TcpClient remoteClient = new TcpClient(turnUri.Host, turnUri.Port))
                        {
                            var remoteStream = remoteClient.GetStream();
                            await await Task.WhenAny(
                                remoteStream.CopyToAsync(stream, bufferSize, cancellationToken),
                                stream.CopyToAsync(remoteStream, bufferSize, cancellationToken));
                        }

                        client.Dispose();
                    },
                    cancellationToken));
            }

            foreach (var client in clients)
            {
                client?.Dispose();
            }

            Log.Debug("TurnProxy is canceled.");

            await Task.WhenAny(tasks);
        }

        private class Sleep : IAction
        {
            public IValue PlainValue => default(Null);

            public IAccountStateDelta Execute(IActionContext context)
            {
                Thread.Sleep(10);
                return context.PreviousStates;
            }

            public void LoadPlainValue(IValue plainValue)
            {
            }
        }
    }
}
