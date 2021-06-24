using System;
using System.Net;
using System.Net.Sockets;
using System.Threading.Tasks;
using Libplanet.Blockchain.Policies;
using Libplanet.Crypto;
using Libplanet.Net;
using Libplanet.Net.Transports;
using Libplanet.Tests.Common.Action;
using Libplanet.Tests.Store;
using NetMQ;
using Xunit;
using Xunit.Sdk;

namespace Libplanet.Tests.Net.Transports
{
    [Collection("NetMQConfiguration")]
    public class BoundPeerExtensionsTest
    {
        [Theory(Timeout = 60 * 1000)]
        [InlineData(SwarmOptions.TransportType.NetMQTransport)]
        [InlineData(SwarmOptions.TransportType.TcpTransport)]
        public async Task QueryAppProtocolVersion(SwarmOptions.TransportType transportType)
        {
            var fx = new DefaultStoreFixture();
            var policy = new BlockPolicy<DumbAction>();
            var blockchain = TestUtils.MakeBlockChain(policy, fx.Store, fx.StateStore);
            var apvKey = new PrivateKey();
            var swarmKey = new PrivateKey();
            AppProtocolVersion apv = AppProtocolVersion.Sign(apvKey, 1);

            string host = IPAddress.Loopback.ToString();
            int port = FreeTcpPort();

            var option = new SwarmOptions
            {
                Type = transportType,
            };

            using (var swarm = new Swarm<DumbAction>(
                blockchain,
                swarmKey,
                apv,
                host: host,
                listenPort: port,
                options: option))
            {
                var peer = new BoundPeer(swarmKey.PublicKey, new DnsEndPoint(host, port));
                // Before swarm starting...
                await Assert.ThrowsAsync<TimeoutException>(async () =>
                {
                    if (swarm.Transport is NetMQTransport)
                    {
                        peer.QueryAppProtocolVersion(timeout: TimeSpan.FromSeconds(1));
                    }
                    else if (swarm.Transport is TcpTransport)
                    {
                        await peer.QueryAppProtocolVersionTcp(timeout: TimeSpan.FromSeconds(1));
                    }
                    else
                    {
                        throw new XunitException(
                            "Each type of transport must have corresponding test case.");
                    }
                });
                _ = swarm.StartAsync();
                try
                {
                    AppProtocolVersion receivedAPV = default;
                    if (swarm.Transport is NetMQTransport)
                    {
                        receivedAPV = peer.QueryAppProtocolVersion();
                    }
                    else if (swarm.Transport is TcpTransport)
                    {
                        receivedAPV = await peer.QueryAppProtocolVersionTcp();
                    }
                    else
                    {
                        throw new XunitException(
                            "Each type of transport must have corresponding test case.");
                    }

                    Assert.Equal(apv, receivedAPV);
                }
                finally
                {
                    await swarm.StopAsync();
                }
            }

            if (transportType == SwarmOptions.TransportType.NetMQTransport)
            {
                NetMQConfig.Cleanup(false);
            }
        }

        private static int FreeTcpPort()
        {
            var l = new TcpListener(IPAddress.Loopback, 0);
            l.Start();
            int port = ((IPEndPoint)l.LocalEndpoint).Port;
            l.Stop();
            return port;
        }
    }
}
