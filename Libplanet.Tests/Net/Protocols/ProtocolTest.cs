using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Libplanet.Crypto;
using Libplanet.Net;
using Libplanet.Net.Protocols;
using Libplanet.Net.Transports;
using Serilog;
using Xunit;
using Xunit.Abstractions;

namespace Libplanet.Tests.Net.Protocols
{
    public class ProtocolTest
    {
        private const int Timeout = 60 * 1000;
        private readonly Dictionary<Address, TestTransport> _transports;

        public ProtocolTest(ITestOutputHelper output)
        {
            const string outputTemplate =
                "{Timestamp:HH:mm:ss}[@{Address}][{ThreadId}] - {Message}";
            Log.Logger = new LoggerConfiguration()
                .MinimumLevel.Verbose()
                .Enrich.WithThreadId()
                .WriteTo.TestOutput(output, outputTemplate: outputTemplate)
                .CreateLogger()
                .ForContext<ProtocolTest>();

            _transports = new Dictionary<Address, TestTransport>();
        }

        [Fact]
        public void KademliaTest()
        {
            var addr1 = new Address("0000000000000000000000000000000000000000");
            var addr2 = new Address("0000000000000000000000000000000000000001");
            var addr3 = new Address("000000000000000000000000000000000000000c");
            var addr4 = new Address("0000000001000001111110001000011001000001");

            Assert.Equal(
                new Address("000000000100000111111000100001100100000d"),
                Kademlia.CalculateDistance(addr3, addr4));

            Assert.Equal(159, Kademlia.CommonPrefixLength(addr1, addr2));
            Assert.Equal(156, Kademlia.CommonPrefixLength(addr1, addr3));
            Assert.Equal(39, Kademlia.CommonPrefixLength(addr1, addr4));

            Assert.True(string.CompareOrdinal(addr1.ToHex(), addr2.ToHex()) < 1);
            Assert.True(string.CompareOrdinal(addr2.ToHex(), addr3.ToHex()) < 1);
            Assert.True(string.CompareOrdinal(addr3.ToHex(), addr4.ToHex()) < 1);
        }

        [Fact(Timeout = Timeout)]
        public async Task Start()
        {
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();

            Assert.Throws<TransportException>(() => transportA.SendPing(transportB.AsPeer));
            await StartTestTransportAsync(transportA);
            await Assert.ThrowsAsync<TimeoutException>(() =>
                transportA.AddPeersAsync(
                    new[] { transportB.AsPeer },
                    TimeSpan.FromMilliseconds(500))
            );
            Assert.Empty(transportA.ReceivedMessages);
        }

        [Fact(Timeout = Timeout)]
        public async Task Ping()
        {
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();

            try
            {
                await StartTestTransportAsync(transportA);
                await StartTestTransportAsync(transportB);
                transportA.SendPing(transportB.AsPeer);
                await transportA.MessageReceived.WaitAsync();
                await Task.Delay(100);

                Assert.Single(transportA.ReceivedMessages);
                Assert.Single(transportB.ReceivedMessages);
                Assert.Contains(transportA.AsPeer, transportB.Peers);
            }
            finally
            {
                await transportA.StopAsync(TimeSpan.Zero);
                await transportB.StopAsync(TimeSpan.Zero);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task PingTwice()
        {
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();

            try
            {
                await StartTestTransportAsync(transportA);
                await StartTestTransportAsync(transportB);

                transportA.SendPing(transportB.AsPeer);
                await transportA.MessageReceived.WaitAsync();
                await transportB.MessageReceived.WaitAsync();
                transportB.SendPing(transportA.AsPeer);
                await transportA.MessageReceived.WaitAsync();
                await transportB.MessageReceived.WaitAsync();

                Assert.Equal(2, transportA.ReceivedMessages.Count);
                Assert.Equal(2, transportB.ReceivedMessages.Count);
                Assert.Contains(transportA.AsPeer, transportB.Peers);
                Assert.Contains(transportB.AsPeer, transportA.Peers);
            }
            finally
            {
                await transportA.StopAsync(TimeSpan.Zero);
                await transportB.StopAsync(TimeSpan.Zero);
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task PingToClosedPeer()
        {
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();
            var transportC = CreateTestTransport();

            await StartTestTransportAsync(transportA);
            await StartTestTransportAsync(transportB);
            await StartTestTransportAsync(transportC);

            await transportA.AddPeersAsync(new[] { transportB.AsPeer, transportC.AsPeer }, null);

            Assert.Contains(transportB.AsPeer, transportA.Peers);
            Assert.Contains(transportC.AsPeer, transportA.Peers);

            await transportC.StopAsync(TimeSpan.Zero);
            await Assert.ThrowsAsync<TimeoutException>(
                () => transportA.AddPeersAsync(
                    new[] { transportC.AsPeer },
                    TimeSpan.FromSeconds(3)));
            await transportA.AddPeersAsync(new[] { transportB.AsPeer }, null);

            Assert.Contains(transportB.AsPeer, transportA.Peers);

            transportA.Dispose();
            transportB.Dispose();
            transportC.Dispose();
        }

        [Fact(Timeout = Timeout)]
        public async Task BootstrapException()
        {
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();

            await Assert.ThrowsAsync<TransportException>(
                () => transportB.BootstrapAsync(
                    new[] { transportA.AsPeer },
                    TimeSpan.FromSeconds(3),
                    TimeSpan.FromSeconds(3))
            );

            transportA.Dispose();
            transportB.Dispose();
        }

        [Fact(Timeout = Timeout)]
        public async Task BootstrapAsyncTest()
        {
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();
            var transportC = CreateTestTransport();

            try
            {
                await StartTestTransportAsync(transportA);
                await StartTestTransportAsync(transportB);
                await StartTestTransportAsync(transportC);

                await transportB.BootstrapAsync(new[] { transportA.AsPeer });
                await transportC.BootstrapAsync(new[] { transportA.AsPeer });

                Assert.Contains(transportB.AsPeer, transportC.Peers);
                Assert.Contains(transportC.AsPeer, transportB.Peers);

                transportA.Table.Clear();
                transportB.Table.Clear();
                transportC.Table.Clear();

                await transportB.AddPeersAsync(new[] { transportC.AsPeer }, null);
                await transportC.StopAsync(TimeSpan.Zero);
                await transportA.BootstrapAsync(new[] { transportB.AsPeer });
                Assert.Contains(transportB.AsPeer, transportA.Peers);
                Assert.DoesNotContain(transportC.AsPeer, transportA.Peers);
            }
            finally
            {
                transportA.Dispose();
                transportB.Dispose();
                transportC.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task RemoveStalePeers()
        {
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();

            await StartTestTransportAsync(transportA);
            await StartTestTransportAsync(transportB);

            await transportA.AddPeersAsync(new[] { transportB.AsPeer }, null);
            Assert.Single(transportA.Peers);

            await transportB.StopAsync(TimeSpan.Zero);
            await Task.Delay(100);
            await transportA.Protocol.RefreshTableAsync(TimeSpan.Zero, default(CancellationToken));
            Assert.Empty(transportA.Peers);

            transportA.Dispose();
            transportB.Dispose();
        }

        [Fact(Timeout = Timeout)]
        public async Task RoutingTableFull()
        {
            var transport = CreateTestTransport(tableSize: 1, bucketSize: 1);
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();
            var transportC = CreateTestTransport();

            await StartTestTransportAsync(transport);
            await StartTestTransportAsync(transportA);
            await StartTestTransportAsync(transportB);
            await StartTestTransportAsync(transportC);

            await transportA.AddPeersAsync(new[] { transport.AsPeer }, null);
            await transportB.AddPeersAsync(new[] { transport.AsPeer }, null);
            await transportC.AddPeersAsync(new[] { transport.AsPeer }, null);

            Assert.Single(transportA.Peers);
            Assert.Contains(transportA.AsPeer, transport.Peers);
            Assert.DoesNotContain(transportB.AsPeer, transport.Peers);
            Assert.DoesNotContain(transportC.AsPeer, transport.Peers);

            transport.Dispose();
            transportA.Dispose();
            transportB.Dispose();
            transportC.Dispose();
        }

        [Fact(Timeout = Timeout)]
        public async Task ReplacementCache()
        {
            var transport = CreateTestTransport(tableSize: 1, bucketSize: 1);
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();
            var transportC = CreateTestTransport();

            await StartTestTransportAsync(transport);
            await StartTestTransportAsync(transportA);
            await StartTestTransportAsync(transportB);
            await StartTestTransportAsync(transportC);

            await transportA.AddPeersAsync(new[] { transport.AsPeer }, null);
            await transportB.AddPeersAsync(new[] { transport.AsPeer }, null);
            await Task.Delay(100);
            await transportC.AddPeersAsync(new[] { transport.AsPeer }, null);

            Assert.Single(transportA.Peers);
            Assert.Contains(transportA.AsPeer, transport.Peers);
            Assert.DoesNotContain(transportB.AsPeer, transport.Peers);

            await transportA.StopAsync(TimeSpan.Zero);
            await transport.Protocol.RefreshTableAsync(TimeSpan.Zero, default(CancellationToken));
            await transport.Protocol.CheckReplacementCacheAsync(default(CancellationToken));

            Assert.Single(transport.Peers);
            Assert.DoesNotContain(transportA.AsPeer, transport.Peers);
            Assert.Contains(transportB.AsPeer, transport.Peers);
            Assert.DoesNotContain(transportC.AsPeer, transport.Peers);

            transport.Dispose();
            transportA.Dispose();
            transportB.Dispose();
            transportC.Dispose();
        }

        [Fact(Timeout = Timeout)]
        public async Task RemoveDeadReplacementCache()
        {
            var transport = CreateTestTransport(tableSize: 1, bucketSize: 1);
            var transportA = CreateTestTransport();
            var transportB = CreateTestTransport();
            var transportC = CreateTestTransport();

            await StartTestTransportAsync(transport);
            await StartTestTransportAsync(transportA);
            await StartTestTransportAsync(transportB);
            await StartTestTransportAsync(transportC);

            await transportA.AddPeersAsync(new[] { transport.AsPeer }, null);
            await transportB.AddPeersAsync(new[] { transport.AsPeer }, null);

            Assert.Single(transport.Peers);
            Assert.Contains(transportA.AsPeer, transport.Peers);
            Assert.DoesNotContain(transportB.AsPeer, transport.Peers);

            await transportA.StopAsync(TimeSpan.Zero);
            await transportB.StopAsync(TimeSpan.Zero);

            await transportC.AddPeersAsync(new[] { transport.AsPeer }, null);
            await transport.Protocol.RefreshTableAsync(TimeSpan.Zero, default(CancellationToken));
            await transport.Protocol.CheckReplacementCacheAsync(default(CancellationToken));

            Assert.Single(transport.Peers);
            Assert.DoesNotContain(transportA.AsPeer, transport.Peers);
            Assert.DoesNotContain(transportB.AsPeer, transport.Peers);
            Assert.Contains(transportC.AsPeer, transport.Peers);

            transport.Dispose();
            transportA.Dispose();
            transportB.Dispose();
            transportC.Dispose();
        }

        [Theory(Timeout = 2 * Timeout)]
        [InlineData(1)]
        [InlineData(5)]
        [InlineData(20)]
        [InlineData(50)]
        public async Task BroadcastMessage(int count)
        {
            var seed = CreateTestTransport();
            await StartTestTransportAsync(seed);
            var transports = new TestTransport[count];
            for (var i = 0; i < count; i++)
            {
                transports[i] = CreateTestTransport();
                await StartTestTransportAsync(transports[i]);
            }

            try
            {
                foreach (var transport in transports)
                {
                    await transport.BootstrapAsync(new[] { seed.AsPeer });
                }

                Log.Debug("Bootstrap completed.");

                var tasks =
                    transports.Select(transport => transport.WaitForTestMessageWithData("foo"));

                seed.BroadcastTestMessage(null, "foo");
                Log.Debug("Broadcast completed.");

                await Task.WhenAll(tasks);
            }
            finally
            {
                seed.Dispose();
                foreach (var transport in transports)
                {
                    Assert.True(transport.ReceivedTestMessageOfData("foo"));
                    transport.Dispose();
                }
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task BroadcastGuarantee()
        {
            // Make sure t1 and t2 is in same bucket of seed's routing table.
            var privateKey0 = new PrivateKey(new byte[]
            {
                0x1a, 0x55, 0x30, 0x84, 0xe8, 0x9e, 0xee, 0x1e, 0x9f, 0xe2, 0xd1, 0x49, 0xe7, 0xa9,
                0x53, 0xa9, 0xb4, 0xe4, 0xfe, 0x5a, 0xc1, 0x6c, 0x61, 0x9f, 0x54, 0x8f, 0x5e, 0xd9,
                0x7f, 0xa3, 0xa0, 0x79,
            });
            var privateKey1 = new PrivateKey(new byte[]
            {
                0x8e, 0x26, 0x31, 0x4a, 0xee, 0x84, 0xd, 0x8a, 0xea, 0x7b, 0x6, 0xf8, 0x81, 0x5f,
                0x69, 0xb3, 0x44, 0x46, 0xe0, 0x27, 0x65, 0x17, 0x1, 0x16, 0x58, 0x26, 0x69, 0x93,
                0x48, 0xbb, 0xf, 0xb4,
            });
            var privateKey2 = new PrivateKey(new byte[]
            {
                0xd4, 0x6b, 0x4b, 0x38, 0xde, 0x39, 0x25, 0x3b, 0xd8, 0x1, 0x9d, 0x2, 0x2, 0x7a,
                0x90, 0x9, 0x46, 0x2f, 0xc1, 0xd3, 0xd9, 0xa, 0xa6, 0xf4, 0xfa, 0x9a, 0x6, 0xa3,
                0x60, 0xed, 0xf3, 0xd7,
            });

            var seed = CreateTestTransport(privateKey0);
            var t1 = CreateTestTransport(privateKey1, true);
            var t2 = CreateTestTransport(privateKey2);
            await StartTestTransportAsync(seed);
            await StartTestTransportAsync(t1);
            await StartTestTransportAsync(t2);

            try
            {
                await t1.BootstrapAsync(new[] { seed.AsPeer });
                await t2.BootstrapAsync(new[] { seed.AsPeer });

                Log.Debug("Bootstrap completed.");

                var tcs = new CancellationTokenSource();
                var task = t2.WaitForTestMessageWithData("foo", tcs.Token);

                seed.BroadcastTestMessage(null, "foo");
                Log.Debug("Broadcast \"foo\" completed.");

                tcs.CancelAfter(TimeSpan.FromSeconds(5));
                await task;

                Assert.True(t2.ReceivedTestMessageOfData("foo"));

                tcs = new CancellationTokenSource();
                task = t2.WaitForTestMessageWithData("bar", tcs.Token);

                seed.BroadcastTestMessage(null, "bar");
                Log.Debug("Broadcast \"bar\" completed.");

                tcs.CancelAfter(TimeSpan.FromSeconds(5));
                await task;

                Assert.True(t2.ReceivedTestMessageOfData("bar"));

                tcs = new CancellationTokenSource();
                task = t2.WaitForTestMessageWithData("baz", tcs.Token);

                seed.BroadcastTestMessage(null, "baz");
                Log.Debug("Broadcast \"baz\" completed.");

                tcs.CancelAfter(TimeSpan.FromSeconds(5));
                await task;

                Assert.True(t2.ReceivedTestMessageOfData("baz"));

                tcs = new CancellationTokenSource();
                task = t2.WaitForTestMessageWithData("qux", tcs.Token);

                seed.BroadcastTestMessage(null, "qux");
                Log.Debug("Broadcast \"qux\" completed.");

                tcs.CancelAfter(TimeSpan.FromSeconds(5));
                await task;

                Assert.True(t2.ReceivedTestMessageOfData("qux"));
            }
            finally
            {
                seed.Dispose();
                t1.Dispose();
                t2.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task DoNotBroadcastToSourcePeer()
        {
            TestTransport transportA = CreateTestTransport(new PrivateKey());
            TestTransport transportB = CreateTestTransport(new PrivateKey());
            TestTransport transportC = CreateTestTransport(new PrivateKey());

            await StartTestTransportAsync(transportA);
            await StartTestTransportAsync(transportB);
            await StartTestTransportAsync(transportC);

            try
            {
                await transportA.AddPeersAsync(new[] { transportB.AsPeer }, null);
                await transportB.AddPeersAsync(new[] { transportC.AsPeer }, null);

                transportA.BroadcastTestMessage(null, "foo");
                await transportC.WaitForTestMessageWithData("foo");
                await Task.Delay(100);

                Assert.True(transportC.ReceivedTestMessageOfData("foo"));
                Assert.False(transportA.ReceivedTestMessageOfData("foo"));
            }
            finally
            {
                transportA.Dispose();
                transportB.Dispose();
                transportC.Dispose();
            }
        }

        [Fact(Timeout = Timeout)]
        public async Task RefreshTable()
        {
            const int peersCount = 10;
            var privateKey = new PrivateKey();
            var privateKeys = Enumerable.Range(0, peersCount).Select(
                i => TestUtils.GeneratePrivateKeyOfBucketIndex(privateKey.ToAddress(), i / 2));
            TestTransport transport = CreateTestTransport(privateKey);
            TestTransport[] transports =
                privateKeys.Select(key => CreateTestTransport(key)).ToArray();

            await StartTestTransportAsync(transport);
            foreach (var t in transports)
            {
                await StartTestTransportAsync(t);
            }

            try
            {
                foreach (var t in transports)
                {
                    transport.Table.AddPeer(
                        (BoundPeer)t.AsPeer,
                        DateTimeOffset.UtcNow - TimeSpan.FromMinutes(2));
                }

                IReadOnlyList<BoundPeer> refreshCandidates =
                    transport.Table.PeersToRefresh(TimeSpan.FromMinutes(1));
                Assert.Equal(peersCount, transport.Peers.Count());
                Assert.Equal(peersCount / 2, refreshCandidates.Count);
                Assert.Equal(peersCount / 2, transport.Table.NonEmptyBuckets.Count());

                await transport.Protocol.RefreshTableAsync(TimeSpan.FromMinutes(1), default);
                Assert.NotEqual(
                    refreshCandidates.ToHashSet(),
                    transport.Table.PeersToRefresh(TimeSpan.FromMinutes(1)).ToHashSet());
                Assert.Equal(
                    peersCount / 2,
                    transport.Table.PeersToRefresh(TimeSpan.FromMinutes(1)).Count());
                Assert.Equal(peersCount / 2, transport.Table.NonEmptyBuckets.Count());

                await transport.Protocol.RefreshTableAsync(TimeSpan.FromMinutes(1), default);
                Assert.Empty(transport.Table.PeersToRefresh(TimeSpan.FromMinutes(1)));
            }
            finally
            {
                transport.Dispose();
                foreach (var t in transports)
                {
                    t.Dispose();
                }
            }
        }

        private TestTransport CreateTestTransport(
            PrivateKey privateKey = null,
            bool blockBroadcast = false,
            int tableSize = Kademlia.TableSize,
            int bucketSize = Kademlia.BucketSize,
            TimeSpan? networkDelay = null)
        {
            return new TestTransport(
                _transports,
                privateKey ?? new PrivateKey(),
                blockBroadcast,
                tableSize,
                bucketSize,
                networkDelay);
        }

        private async Task StartTestTransportAsync(
            TestTransport transport,
            CancellationToken cancellationToken = default(CancellationToken))
        {
            _ = transport.StartAsync(cancellationToken);
            await transport.WaitForRunningAsync();
        }
    }
}
