using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Net;
using System.Threading;
using System.Threading.Tasks;
using Libplanet.Crypto;
using Libplanet.Net;
using Libplanet.Net.Messages;
using Libplanet.Net.Protocols;
using Libplanet.Net.Transports;
using Nito.AsyncEx;
using Serilog;
using Xunit;
using Xunit.Abstractions;

namespace Libplanet.Tests.Net.Transports
{
    public class NetMQTransportTest : TransportTest
    {
        public NetMQTransportTest(ITestOutputHelper testOutputHelper)
        {
            TransportConstructor = (
                    table,
                    privateKey,
                    appProtocolVersion,
                    trustedAppProtocolVersionSigners,
                    host,
                    listenPort,
                    iceServers,
                    differentAppProtocolVersionEncountered,
                    messageLifespan
                )
                => CreateNetMQTransport(
                    table,
                    privateKey,
                    appProtocolVersion,
                    trustedAppProtocolVersionSigners,
                    50,
                    host,
                    listenPort,
                    iceServers,
                    differentAppProtocolVersionEncountered,
                    messageLifespan);

            const string outputTemplate =
                "{Timestamp:HH:mm:ss:ffffff}[{ThreadId}] - {Message}";
            Log.Logger = new LoggerConfiguration()
                .MinimumLevel.Verbose()
                .Enrich.WithThreadId()
                .WriteTo.TestOutput(testOutputHelper, outputTemplate: outputTemplate)
                .CreateLogger()
                .ForContext<NetMQTransportTest>();
            Logger = Log.ForContext<NetMQTransportTest>();
        }

        [SkippableFact(Timeout = Timeout, Skip = "Target method is broken.")]
        public async Task MessageHistory()
        {
            var transportA = CreateNetMQTransport();
            var transportB = CreateNetMQTransport();

            var messageReceived = new AsyncAutoResetEvent();
            transportB.ProcessMessageHandler.Register(async message =>
            {
                messageReceived.Set();
                await Task.Yield();
            });

            try
            {
                await InitializeAsync(transportA);
                await InitializeAsync(transportB);
                var boundPeer = (BoundPeer)transportB.AsPeer;
                Task t = messageReceived.WaitAsync();
                await transportA.SendMessageAsync(boundPeer, new Ping(), CancellationToken.None);
                await t;
                t = messageReceived.WaitAsync();
                await transportA.SendMessageAsync(boundPeer, new Pong(), CancellationToken.None);
                await t;

                transportB.MessageHistory.TryDequeue(out var message1);
                transportB.MessageHistory.TryDequeue(out var message2);
                Assert.IsType<Ping>(message1);
                Assert.Equal(transportA.AsPeer, message1?.Remote);
                Assert.IsType<Pong>(message2);
                Assert.Equal(transportA.AsPeer, message2?.Remote);
            }
            finally
            {
                transportA.Dispose();
                transportB.Dispose();
            }
        }

        private NetMQTransport CreateNetMQTransport(
            PrivateKey privateKey = null,
            int tableSize = 160,
            int bucketSize = 16,
            AppProtocolVersion appProtocolVersion = default,
            IImmutableSet<PublicKey> trustedAppProtocolVersionSigners = null,
            int workers = 50,
            string host = null,
            int? listenPort = null,
            IEnumerable<IceServer> iceServers = null,
            DifferentAppProtocolVersionEncountered differentAppProtocolVersionEncountered = null,
            TimeSpan? messageLifespan = null
        )
        {
            privateKey = privateKey ?? new PrivateKey();
            host = host ?? IPAddress.Loopback.ToString();
            var table = new RoutingTable(privateKey.ToAddress(), tableSize, bucketSize);

            return new NetMQTransport(
                table,
                privateKey,
                appProtocolVersion,
                trustedAppProtocolVersionSigners,
                workers,
                host,
                listenPort,
                iceServers,
                differentAppProtocolVersionEncountered,
                messageLifespan);
        }

        private NetMQTransport CreateNetMQTransport(
            RoutingTable table,
            PrivateKey privateKey,
            AppProtocolVersion appProtocolVersion,
            IImmutableSet<PublicKey> trustedAppProtocolVersionSigners,
            int workers,
            string host,
            int? listenPort,
            IEnumerable<IceServer> iceServers,
            DifferentAppProtocolVersionEncountered differentAppProtocolVersionEncountered,
            TimeSpan? messageLifespan
        )
        {
            return new NetMQTransport(
                table,
                privateKey,
                appProtocolVersion,
                trustedAppProtocolVersionSigners,
                workers,
                host,
                listenPort,
                iceServers,
                differentAppProtocolVersionEncountered,
                messageLifespan);
        }
    }
}
