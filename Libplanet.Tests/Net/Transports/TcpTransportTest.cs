using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Threading.Tasks;
using Libplanet.Crypto;
using Libplanet.Net;
using Libplanet.Net.Messages;
using Libplanet.Net.Protocols;
using Libplanet.Net.Transports;
using Serilog;
using Xunit;
using Xunit.Abstractions;

namespace Libplanet.Tests.Net.Transports
{
    public class TcpTransportTest : TransportTest
    {
        public TcpTransportTest(ITestOutputHelper testOutputHelper)
        {
            TransportConstructor = CreateTcpTransport;

            const string outputTemplate =
                "{Timestamp:HH:mm:ss:ffffff}[{ThreadId}] - {Message}";
            Log.Logger = new LoggerConfiguration()
                .MinimumLevel.Verbose()
                .Enrich.WithThreadId()
                .WriteTo.TestOutput(testOutputHelper, outputTemplate: outputTemplate)
                .CreateLogger()
                .ForContext<TransportTest>();
            Logger = Log.ForContext<TransportTest>();
        }

        [SkippableFact(Timeout = Timeout)]
        public async Task ReadWriteMessageWithInvalidMagicCookieAsync()
        {
            byte[] invalidCookie = { 0x01, 0x02 };
            Assert.False(TcpTransport.MagicCookie.SequenceEqual(invalidCookie));

            var listener = new TcpListener(IPAddress.Any, 0);
            listener.Start();
            var client = new TcpClient();
            await client.ConnectAsync("127.0.0.1", ((IPEndPoint)listener.LocalEndpoint).Port);
            TcpClient listenerSocket = await listener.AcceptTcpClientAsync();

            AppProtocolVersion version = AppProtocolVersion.Sign(new PrivateKey(), 1);
            TcpTransport transport = CreateTcpTransport(appProtocolVersion: version);
            try
            {
                var message = new Ping
                {
                    Identity = Guid.NewGuid().ToByteArray(),
                };

                byte[] serialized = message.Serialize(
                    new PrivateKey(),
                    transport.AsPeer,
                    DateTimeOffset.UtcNow,
                    version);
                int length = serialized.Length;
                var buffer = new byte[invalidCookie.Length + sizeof(int) + length];
                invalidCookie.CopyTo(buffer, 0);
                BitConverter.GetBytes(length).CopyTo(buffer, invalidCookie.Length);
                serialized.CopyTo(buffer, invalidCookie.Length + sizeof(int));
                NetworkStream stream = client.GetStream();
                await stream.WriteAsync(buffer, 0, buffer.Length, default);
                await Assert.ThrowsAsync<InvalidMagicCookieException>(
                    async () => await transport.ReadMessageAsync(listenerSocket, default));

                byte[] shortBuffer = { 0x00 };
                await stream.WriteAsync(shortBuffer, 0, shortBuffer.Length, default);
                await Assert.ThrowsAsync<InvalidMagicCookieException>(
                    async () => await transport.ReadMessageAsync(listenerSocket, default));
            }
            finally
            {
                listenerSocket.Dispose();
                client.Dispose();
            }
        }

        private TcpTransport CreateTcpTransport(
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
            privateKey = privateKey ?? new PrivateKey();
            host = host ?? IPAddress.Loopback.ToString();
            trustedAppProtocolVersionSigners = trustedAppProtocolVersionSigners ??
                                               ImmutableHashSet<PublicKey>.Empty;
            iceServers = iceServers ?? new IceServer[] { };
            var table = new RoutingTable(privateKey.ToAddress(), tableSize, bucketSize);

            return CreateTcpTransport(
                table,
                privateKey,
                appProtocolVersion,
                trustedAppProtocolVersionSigners,
                host,
                listenPort,
                iceServers,
                differentAppProtocolVersionEncountered,
                messageLifespan);
        }

        private TcpTransport CreateTcpTransport(
            RoutingTable table,
            PrivateKey privateKey,
            AppProtocolVersion appProtocolVersion,
            IImmutableSet<PublicKey> trustedAppProtocolVersionSigners,
            string host,
            int? listenPort,
            IEnumerable<IceServer> iceServers,
            DifferentAppProtocolVersionEncountered differentAppProtocolVersionEncountered,
            TimeSpan? messageLifespan
        )
        {
            return new TcpTransport(
                table,
                privateKey,
                appProtocolVersion,
                trustedAppProtocolVersionSigners,
                host,
                listenPort,
                iceServers,
                differentAppProtocolVersionEncountered,
                messageLifespan);
        }
    }
}
