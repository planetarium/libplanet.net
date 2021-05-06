using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Net;
using System.Threading;
using System.Threading.Tasks;
using Libplanet.Crypto;
using Libplanet.Net;
using Libplanet.Net.Messages;
using Libplanet.Net.Protocols;
using Libplanet.Net.Transports;
using Serilog;
using Xunit;
using Xunit.Sdk;

namespace Libplanet.Tests.Net.Transports
{
    public abstract class TransportTest
    {
        protected const int Timeout = 60 * 1000;

        protected ILogger Logger { get; set; }

        protected Func<RoutingTable, PrivateKey, AppProtocolVersion, IImmutableSet<PublicKey>,
            string, int?, IEnumerable<IceServer>, DifferentAppProtocolVersionEncountered,
            TimeSpan?, ITransport>
            TransportConstructor { get; set; }

        [SkippableFact(Timeout = Timeout)]
        public void StartAsync()
        {
            ITransport transport = CreateTransport();

            try
            {
                _ = transport.StartAsync();
                Assert.True(transport.Running);
            }
            finally
            {
                transport.Dispose();
            }
        }

        [SkippableFact(Timeout = Timeout)]
        public async void RestartAsync()
        {
            ITransport transport = CreateTransport();

            try
            {
                await InitializeAsync(transport);
                Assert.True(transport.Running);
                await transport.StopAsync(TimeSpan.Zero);
                Assert.False(transport.Running);
                await InitializeAsync(transport);
                Assert.True(transport.Running);
            }
            finally
            {
                transport.Dispose();
            }
        }

        [SkippableFact(Timeout = Timeout)]
        public async void Dispose()
        {
            ITransport transport = CreateTransport();

            try
            {
                await InitializeAsync(transport);
                Assert.True(transport.Running);
                transport.Dispose();
                var boundPeer = new BoundPeer(
                    new PrivateKey().PublicKey,
                    new DnsEndPoint("localhost", 1234));
                var message = new Ping();
                await Assert.ThrowsAsync<ObjectDisposedException>(
                    async () => await transport.StartAsync());
                await Assert.ThrowsAsync<ObjectDisposedException>(
                    async () => await transport.StopAsync(TimeSpan.Zero));
                await Assert.ThrowsAsync<ObjectDisposedException>(
                    async () => await transport.SendMessageAsync(boundPeer, message, default));
                await Assert.ThrowsAsync<ObjectDisposedException>(
                    async () => await transport.SendMessageWithReplyAsync(
                        boundPeer,
                        message,
                        null,
                        default));
                await Assert.ThrowsAsync<ObjectDisposedException>(
                    async () => await transport.SendMessageWithReplyAsync(
                        boundPeer,
                        message,
                        null,
                        3,
                        default));
                Assert.Throws<ObjectDisposedException>(
                    () => transport.BroadcastMessage(null, message));
                Assert.Throws<ObjectDisposedException>(
                    () => transport.ReplyMessage(message));

                // To check multiple Dispose() throws error or not.
                transport.Dispose();
            }
            finally
            {
                transport.Dispose();
            }
        }

        [SkippableFact(Timeout = Timeout)]
        public async Task AsPeer()
        {
            var privateKey = new PrivateKey();
            var boundPrivateKey = new PrivateKey();
            string host = IPAddress.Loopback.ToString();
            const int listenPort = 50000;
            ITransport transport = CreateTransport(privateKey: privateKey);
            ITransport boundTransport = CreateTransport(
                privateKey: boundPrivateKey,
                host: host,
                listenPort: listenPort);

            try
            {
                var peer = transport.AsPeer;
                Assert.IsType<Peer>(peer);
                Assert.IsNotType<BoundPeer>(peer);
                Assert.Equal(privateKey.ToAddress(), peer.Address);

                await InitializeAsync(transport);
                peer = transport.AsPeer;
                Assert.IsNotType<Peer>(peer);
                Assert.IsType<BoundPeer>(peer);
                Assert.Equal(privateKey.ToAddress(), peer.Address);

                peer = boundTransport.AsPeer;
                Assert.IsType<BoundPeer>(peer);
                var boundPeer = (BoundPeer)peer;
                Assert.Equal(boundPrivateKey.ToAddress(), boundPeer.Address);
                Assert.Equal(listenPort, boundPeer.EndPoint.Port);
                Assert.Equal(host, boundPeer.EndPoint.Host);
            }
            finally
            {
                transport.Dispose();
                boundTransport.Dispose();
            }
        }

        [SkippableFact(Timeout = Timeout, Skip = "Target method is broken.")]
        public async Task SendMessageAsync()
        {
            ITransport transportA = CreateTransport();
            ITransport transportB = CreateTransport();

            TaskCompletionSource<Message> tcs = new TaskCompletionSource<Message>();

            transportB.ProcessMessageHandler += (sender, message) =>
            {
                tcs.SetResult(message);
            };

            try
            {
                await InitializeAsync(transportA);
                await InitializeAsync(transportB);

                Assert.True(transportA.Running);
                Assert.True(transportB.Running);

                await transportA.SendMessageAsync(
                    (BoundPeer)transportB.AsPeer,
                    new Ping(),
                    CancellationToken.None);

                Message message = await tcs.Task;

                Assert.IsType<Ping>(message);
            }
            finally
            {
                transportA.Dispose();
                transportB.Dispose();
            }
        }

        // This also tests ITransport.ReplyMessage at the same time.
        [SkippableFact(Timeout = Timeout)]
        public async Task SendMessageWithReplyAsync()
        {
            ITransport transportA = CreateTransport();
            ITransport transportB = CreateTransport();

            transportB.ProcessMessageHandler += (sender, message) =>
            {
                if (message is Ping)
                {
                    transportB.ReplyMessage(new Pong
                    {
                        Identity = message.Identity,
                    });
                }
            };

            try
            {
                await InitializeAsync(transportA);
                await InitializeAsync(transportB);

                Message reply = await transportA.SendMessageWithReplyAsync(
                    (BoundPeer)transportB.AsPeer,
                    new Ping(),
                    null,
                    CancellationToken.None);

                Assert.IsType<Pong>(reply);
            }
            finally
            {
                transportA.Dispose();
                transportB.Dispose();
            }
        }

        [SkippableFact(Timeout = Timeout)]
        public async Task BroadcastMessage()
        {
            var address = new PrivateKey().ToAddress();
            ITransport transportA = null;
            ITransport transportB = CreateTransport(
                privateKey: TestUtils.GeneratePrivateKeyOfBucketIndex(address, 0));
            ITransport transportC = CreateTransport(
                privateKey: TestUtils.GeneratePrivateKeyOfBucketIndex(address, 1));
            ITransport transportD = CreateTransport(
                privateKey: TestUtils.GeneratePrivateKeyOfBucketIndex(address, 2));

            var tcsB = new TaskCompletionSource<Message>();
            var tcsC = new TaskCompletionSource<Message>();
            var tcsD = new TaskCompletionSource<Message>();

            transportB.ProcessMessageHandler += MessageHandler(tcsB);
            transportC.ProcessMessageHandler += MessageHandler(tcsC);
            transportD.ProcessMessageHandler += MessageHandler(tcsD);

            EventHandler<Message> MessageHandler(TaskCompletionSource<Message> tcs)
            {
                return (sender, message) =>
                {
                    if (message is Ping)
                    {
                        tcs.SetResult(message);
                    }
                };
            }

            try
            {
                await InitializeAsync(transportB);
                await InitializeAsync(transportC);
                await InitializeAsync(transportD);

                var table = new RoutingTable(address, bucketSize: 1);
                table.AddPeer(transportB.AsPeer as BoundPeer);
                table.AddPeer(transportC.AsPeer as BoundPeer);
                table.AddPeer(transportD.AsPeer as BoundPeer);

                transportA = CreateTransport(table);
                await InitializeAsync(transportA);

                Logger?.Debug("Stop1");

                transportA.BroadcastMessage(transportD.AsPeer.Address, new Ping());

                await Task.WhenAll(tcsB.Task, tcsC.Task);

                Logger?.Debug("Stop2");

                Assert.IsType<Ping>(tcsB.Task.Result);
                Assert.IsType<Ping>(tcsC.Task.Result);
                Assert.False(tcsD.Task.IsCompleted);

                tcsD.SetCanceled();
            }
            finally
            {
                transportA?.Dispose();
                transportB.Dispose();
                transportC.Dispose();
                transportD.Dispose();
            }
        }

        protected async Task InitializeAsync(
            ITransport transport,
            CancellationToken cts = default)
        {
            _ = transport.StartAsync(cts);
            await transport.WaitForRunningAsync();
        }

        private ITransport CreateTransport(
            PrivateKey privateKey = null,
            int tableSize = 160,
            int bucketSize = 16,
            AppProtocolVersion appProtocolVersion = default,
            IImmutableSet<PublicKey> trustedAppProtocolVersionSigners = null,
            string host = null,
            int? listenPort = null,
            IEnumerable<IceServer> iceServers = null,
            DifferentAppProtocolVersionEncountered differentAppProtocolVersionEncountered = null,
            TimeSpan? messageLifespan = null
        )
        {
            if (TransportConstructor is null)
            {
                throw new XunitException("Transport constructor is not defined.");
            }

            privateKey = privateKey ?? new PrivateKey();
            host = host ?? IPAddress.Loopback.ToString();
            var routingTable = new RoutingTable(privateKey.ToAddress(), tableSize, bucketSize);

            return CreateTransport(
                routingTable,
                privateKey,
                appProtocolVersion,
                trustedAppProtocolVersionSigners ?? ImmutableHashSet<PublicKey>.Empty,
                host,
                listenPort,
                iceServers ?? Enumerable.Empty<IceServer>(),
                differentAppProtocolVersionEncountered,
                messageLifespan);
        }

        private ITransport CreateTransport(
            RoutingTable routingTable,
            PrivateKey privateKey = null,
            AppProtocolVersion appProtocolVersion = default,
            IImmutableSet<PublicKey> trustedAppProtocolVersionSigners = null,
            string host = null,
            int? listenPort = null,
            IEnumerable<IceServer> iceServers = null,
            DifferentAppProtocolVersionEncountered differentAppProtocolVersionEncountered = null,
            TimeSpan? messageLifespan = null
        )
        {
            if (TransportConstructor is null)
            {
                throw new XunitException("Transport constructor is not defined.");
            }

            privateKey = privateKey ?? new PrivateKey();
            host = host ?? IPAddress.Loopback.ToString();

            return TransportConstructor(
                routingTable,
                privateKey,
                appProtocolVersion,
                trustedAppProtocolVersionSigners ?? ImmutableHashSet<PublicKey>.Empty,
                host,
                listenPort,
                iceServers ?? Enumerable.Empty<IceServer>(),
                differentAppProtocolVersionEncountered,
                messageLifespan);
        }
    }
}
