using System;
using System.Net.Sockets;
using System.Threading;
using System.Threading.Tasks;
using Libplanet.Crypto;
using Libplanet.Net.Messages;
using NetMQ;
using NetMQ.Sockets;

namespace Libplanet.Net.Transports
{
    /// <summary>
    /// This extension class activates transport-oriented methods on <see cref="BoundPeer"/>.
    /// </summary>
    /// <seealso cref="BoundPeer"/>
    public static class BoundPeerExtensions
    {
        /// <summary>
        /// Queries <see cref="AppProtocolVersion"/> of given <see cref="BoundPeer"/>.
        /// </summary>
        /// <param name="peer">The <see cref="BoundPeer"/> to query
        /// <see cref="AppProtocolVersion"/>.</param>
        /// <param name="timeout">Timeout value for request.</param>
        /// <returns><see cref="AppProtocolVersion"/> of given peer. </returns>
        public static AppProtocolVersion QueryAppProtocolVersion(
            this BoundPeer peer,
            TimeSpan? timeout = null
        )
        {
            using var dealerSocket = new DealerSocket(ToNetMQAddress(peer));
            var key = new PrivateKey();
            var ping = new Ping();
            NetMQMessage request = ping.ToNetMQMessage(
                key,
                new Peer(key.PublicKey),
                DateTimeOffset.UtcNow,
                default
            );

            TimeSpan timeoutNotNull = timeout ?? TimeSpan.FromSeconds(5);
            if (dealerSocket.TrySendMultipartMessage(timeoutNotNull, request))
            {
                var response = new NetMQMessage();
                if (dealerSocket.TryReceiveMultipartMessage(timeoutNotNull, ref response))
                {
                    return AppProtocolVersion.FromToken(response.First.ConvertToString());
                }
            }

            throw new TimeoutException(
                $"Peer[{peer}] didn't respond within the specified time[{timeout}]."
            );
        }

        /// <summary>
        /// Queries <see cref="AppProtocolVersion"/> of given <see cref="BoundPeer"/>
        /// specialized for TCP based transport.
        /// </summary>
        /// <param name="peer">The <see cref="BoundPeer"/> to query
        /// <see cref="AppProtocolVersion"/>.</param>
        /// <param name="timeout">Timeout value for request.</param>
        /// <param name="cancellationToken">
        /// A cancellation token used to propagate notification that this
        /// operation should be canceled.</param>
        /// <returns><see cref="AppProtocolVersion"/> of given peer. </returns>
        public static async Task<AppProtocolVersion> QueryAppProtocolVersionTcp(
            this BoundPeer peer,
            TimeSpan? timeout = null,
            CancellationToken cancellationToken = default
        )
        {
            using var client = new TcpClient();
            await client.ConnectAsync(peer.EndPoint.Host, peer.EndPoint.Port);
            client.ReceiveTimeout = timeout?.Milliseconds ?? 0;
            using var stream = client.GetStream();
            var key = new PrivateKey();
            var ping = new Ping
            {
                Identity = Guid.NewGuid().ToByteArray(),
            };

            byte[] serialized = ping.Serialize(
                key,
                peer,
                DateTimeOffset.UtcNow,
                default);
            int length = serialized.Length;
            var buffer = new byte[TcpTransport.MagicCookie.Length + sizeof(int) + length];
            TcpTransport.MagicCookie.CopyTo(buffer, 0);
            BitConverter.GetBytes(length).CopyTo(buffer, TcpTransport.MagicCookie.Length);
            serialized.CopyTo(buffer, TcpTransport.MagicCookie.Length + sizeof(int));
            await stream.WriteAsync(buffer, 0, buffer.Length, cancellationToken);

            buffer = new byte[1000000];
            int bytesRead = await stream.ReadAsync(buffer, 0, buffer.Length, cancellationToken);
            var magicCookieBuffer = new byte[TcpTransport.MagicCookie.Length];
            Array.Copy(buffer, 0, magicCookieBuffer, 0, TcpTransport.MagicCookie.Length);
            var sizeBuffer = new byte[sizeof(int)];
            Array.Copy(buffer, TcpTransport.MagicCookie.Length, sizeBuffer, 0, sizeof(int));
            length = BitConverter.ToInt32(sizeBuffer, 0);
            var contentBuffer = new byte[length];
            Array.Copy(
                buffer,
                TcpTransport.MagicCookie.Length + sizeof(int),
                contentBuffer,
                0,
                length);

            // length of identity
            Array.Copy(contentBuffer, 4, sizeBuffer, 0, 4);
            length = BitConverter.ToInt32(sizeBuffer, 0);

            // length of apv token
            Array.Copy(contentBuffer, 4 + 4 + length, sizeBuffer, 0, 4);
            int apvLength = BitConverter.ToInt32(sizeBuffer, 0);
            var apvBytes = new byte[apvLength];
            Array.Copy(contentBuffer, 4 + 4 + length + 4, apvBytes, 0, apvLength);
            var frame = new NetMQFrame(apvBytes);
            string token = frame.ConvertToString();
            AppProtocolVersion version = AppProtocolVersion.FromToken(token);
            return version;
        }

        internal static string ToNetMQAddress(this BoundPeer peer)
        {
            return $"tcp://{peer.EndPoint.Host}:{peer.EndPoint.Port}";
        }
    }
}
