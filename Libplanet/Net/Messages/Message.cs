using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Runtime.Serialization.Formatters.Binary;
using Destructurama.Attributed;
using Libplanet.Blocks;
using Libplanet.Crypto;
using Libplanet.Net.Transports;
using NetMQ;

namespace Libplanet.Net.Messages
{
    /// <summary>
    /// Serves as the base class for messages used in <see cref="ITransport"/>.
    /// </summary>
    public abstract class Message
    {
        /// <summary>
        /// The number of frames that all messages commonly contain.
        /// </summary>
        public const int CommonFrames = 5;

        internal const string TimestampFormat = "yyyy-MM-ddTHH:mm:ss.ffffffZ";

        /// <summary>
        /// <c>Enum</c> represents the type of the <see cref="Message"/>.
        /// </summary>
        public enum MessageType : byte
        {
            /// <summary>
            /// Check message to determine peer is alive.
            /// </summary>
            Ping = 0x01,

            /// <summary>
            /// A reply to <see cref="Ping"/>.
            /// </summary>
            Pong = 0x14,

            /// <summary>
            /// Request to query block hashes.
            /// </summary>
            GetBlockHashes = 0x04,

            /// <summary>
            /// Inventory to transfer transactions.
            /// </summary>
            TxIds = 0x06,

            /// <summary>
            /// Request to query blocks.
            /// </summary>
            GetBlocks = 0x07,

            /// <summary>
            /// Request to query transactions.
            /// </summary>
            GetTxs = 0x08,

            /// <summary>
            /// Message containing serialized blocks.
            /// </summary>
            Blocks = 0x0a,

            /// <summary>
            /// Message containing serialized transaction.
            /// </summary>
            Tx = 0x10,

            /// <summary>
            /// Message containing request for nearby peers.
            /// </summary>
            FindNeighbors = 0x11,

            /// <summary>
            /// Message containing nearby peers.
            /// </summary>
            Neighbors = 0x12,

            /// <summary>
            /// Message containing a single <see cref="BlockHeader"/>.
            /// </summary>
            BlockHeaderMessage = 0x0c,

            /// <summary>
            /// Message containing demand block hashes with their index numbers.
            /// </summary>
            BlockHashes = 0x0e,

            /// <summary>
            /// Request current chain status of the peer.
            /// </summary>
            GetChainStatus = 0x20,

            /// <summary>
            /// A reply to <see cref="GetChainStatus"/>.
            /// Contains the chain status of the peer at the moment.
            /// </summary>
            ChainStatus = 0x25,

            /// <summary>
            /// A reply to any messages with different <see cref="AppProtocolVersion"/>.
            /// Contains the expected and actual <see cref="AppProtocolVersion"/>
            /// value of the message.
            /// </summary>
            DifferentVersion = 0x30,
        }

        private enum MessageFrame
        {
            /// <summary>
            /// Frame containing <see cref="AppProtocolVersion"/>.
            /// </summary>
            Version = 0,

            /// <summary>
            /// Frame containing <see cref="MessageType"/>.
            /// </summary>
            Type = 1,

            /// <summary>
            /// Frame containing the sender <see cref="Peer"/> of the <see cref="Message"/>.
            /// </summary>
            Peer = 2,

            /// <summary>
            /// Frame containing the datetime when the <see cref="Message"/> is created.
            /// </summary>
            Timestamp = 3,

            /// <summary>
            /// Frame containing signature of the <see cref="Message"/>.
            /// </summary>
            Sign = 4,
        }

        /// <summary>
        /// <c>byte[]</c>-typed identity of the message.
        /// If a message B is the reply of the message A,
        /// B's identity must be set to A's identity.
        /// </summary>
        public byte[] Identity { get; set; }

        /// <summary>
        /// <see cref="AppProtocolVersion"/>-typed version of the
        /// <see cref="Remote"/>'s transport layer.
        /// </summary>
        [LogAsScalar]
        public AppProtocolVersion Version { get; set; }

        /// <summary>
        /// The timestamp of the message is created.
        /// </summary>
        public DateTimeOffset Timestamp { get; set; }

        /// <summary>
        /// The sender <see cref="Peer"/> of the message.
        /// </summary>
        [LogAsScalar]
        public Peer Remote { get; set; }

        protected abstract MessageType Type { get; }

        protected abstract IEnumerable<NetMQFrame> DataFrames { get; }

        /// <summary>
        /// Casts given <see cref="NetMQMessage"/>-typed <paramref name="raw"/> into
        /// <see cref="Message"/> and checks its validity.
        /// <seealso cref="ToNetMQMessage"/>
        /// </summary>
        /// <param name="raw">A <see cref="NetMQMessage"/> to parse.</param>
        /// <param name="reply">A flag to express whether the target is a reply of other message.
        /// </param>
        /// <param name="localVersion">The <see cref="AppProtocolVersion"/>-typed version of the
        /// local transport layer. <seealso cref="ITransport"/></param>
        /// <param name="trustedAppProtocolVersionSigners"><see cref="PublicKey"/>s of parties
        /// to trust <see cref="AppProtocolVersion"/>s they signed.  To trust any party, pass
        /// <c>null</c>.</param>
        /// <param name="differentAppProtocolVersionEncountered">A delegate called back when a peer
        /// with one different from <paramref name="localVersion"/>, and their version is
        /// signed by a trusted party (i.e., <paramref name="trustedAppProtocolVersionSigners"/>).
        /// If this callback returns <c>false</c>, an encountered peer is ignored.  If this callback
        /// is omitted, all peers with different <see cref="AppProtocolVersion"/>s are ignored.
        /// </param>
        /// <param name="lifetime">
        /// The lifetime of a message.
        /// Messages generated before this value from the current time are ignored.
        /// If <c>null</c> is given, messages will not be ignored by its timestamp.</param>
        /// <returns>A <see cref="Message"/> parsed from <paramref name="raw"/>.</returns>
        /// <exception cref="ArgumentException">Thrown when empty <paramref name="raw"/> is given.
        /// </exception>
        /// <exception cref="DifferentAppProtocolVersionException">Thrown when
        /// <paramref name="localVersion"/> does not match with given <paramref name="raw"/>'s
        /// <see cref="Version"/>, and their version is signed by a trusted party
        /// (i.e., <paramref name="trustedAppProtocolVersionSigners"/>), and
        /// <paramref name="differentAppProtocolVersionEncountered"/> is <c>null</c> or its
        /// return value is <c>false</c>.</exception>
        /// <exception cref="InvalidMessageException">Thrown when given <paramref name="raw"/>'s
        /// signer is invalid.</exception>
        public static Message Parse(
            NetMQMessage raw,
            bool reply,
            AppProtocolVersion localVersion,
            IImmutableSet<PublicKey> trustedAppProtocolVersionSigners,
            DifferentAppProtocolVersionEncountered differentAppProtocolVersionEncountered,
            TimeSpan? lifetime)
        {
            if (raw.FrameCount == 0)
            {
                throw new ArgumentException("Can't parse empty NetMQMessage.");
            }

            // (reply == true)  [version, type, peer, timestamp, sign, frames...]
            // (reply == false) [identity, version, type, peer, timestamp, sign, frames...]
            NetMQFrame[] remains = reply ? raw.ToArray() : raw.Skip(1).ToArray();

            var versionToken = remains[(int)MessageFrame.Version].ConvertToString();

            AppProtocolVersion remoteVersion = AppProtocolVersion.FromToken(versionToken);
            Peer remotePeer = null;
            try
            {
                remotePeer = DeserializePeer(remains[(int)MessageFrame.Peer].ToByteArray());
            }
            catch (Exception)
            {
                // If failed to find out remotePeer, leave it null.
            }

            if (!IsAppProtocolVersionValid(
                remotePeer,
                localVersion,
                remoteVersion,
                trustedAppProtocolVersionSigners,
                differentAppProtocolVersionEncountered))
            {
                throw new DifferentAppProtocolVersionException(
                    "Received message's version is not valid.",
                    reply ? null : raw[0].Buffer.ToArray(),
                    localVersion,
                    remoteVersion);
            }

            var rawType = (MessageType)remains[(int)MessageFrame.Type].ConvertToInt32();
            var ticks = remains[(int)MessageFrame.Timestamp].ConvertToInt64();
            var timestamp = new DateTimeOffset(ticks, TimeSpan.Zero);

            var currentTime = DateTimeOffset.UtcNow;
            if (!(lifetime is null) &&
                (currentTime < timestamp || timestamp + lifetime < currentTime))
            {
                var msg = $"Received message is invalid, created at " +
                          $"{timestamp.ToString(TimestampFormat, CultureInfo.InvariantCulture)} " +
                          $"but designated lifetime is {lifetime} and the current datetime " +
                          $"offset is " +
                          $"{currentTime.ToString(TimestampFormat, CultureInfo.InvariantCulture)}.";
                throw new InvalidTimestampException(msg, timestamp, lifetime.Value, currentTime);
            }

            byte[] signature = remains[(int)MessageFrame.Sign].ToByteArray();

            NetMQFrame[] body = remains.Skip(CommonFrames).ToArray();

            // FIXME: The below code is too repetitive and prone to miss to add, which means,
            // when you add a new message type, you adds an enum member to MessageType and
            // a corresponding subclass of Message, but misses to add that correspondence here,
            // you may take a long time to be aware you've missed here, because the code is still
            // built well and it looks like just Swarm<T> silently ignore new messages.
            // At least this correspondence map should not be here.
            var types = new Dictionary<MessageType, Type>
            {
                { MessageType.Ping, typeof(Ping) },
                { MessageType.Pong, typeof(Pong) },
                { MessageType.GetBlockHashes, typeof(GetBlockHashes) },
                { MessageType.BlockHashes, typeof(BlockHashes) },
                { MessageType.TxIds, typeof(TxIds) },
                { MessageType.GetBlocks, typeof(GetBlocks) },
                { MessageType.GetTxs, typeof(GetTxs) },
                { MessageType.Blocks, typeof(Blocks) },
                { MessageType.Tx, typeof(Tx) },
                { MessageType.FindNeighbors, typeof(FindNeighbors) },
                { MessageType.Neighbors, typeof(Neighbors) },
                { MessageType.BlockHeaderMessage, typeof(BlockHeaderMessage) },
                { MessageType.GetChainStatus, typeof(GetChainStatus) },
                { MessageType.ChainStatus, typeof(ChainStatus) },
                { MessageType.DifferentVersion, typeof(DifferentVersion) },
            };

            if (!types.TryGetValue(rawType, out Type type))
            {
                throw new ArgumentException(
                    $"Can't determine NetMQMessage. [type: {rawType}]",
                    nameof(raw)
                );
            }

            var message = (Message)Activator.CreateInstance(
                type, new[] { body });
            message.Version = remoteVersion;
            message.Remote = remotePeer;
            message.Timestamp = timestamp;

            var headerWithoutSign = new[]
            {
                remains[(int)MessageFrame.Version],
                remains[(int)MessageFrame.Type],
                remains[(int)MessageFrame.Peer],
                remains[(int)MessageFrame.Timestamp],
            };

            var messageForVerify = headerWithoutSign.Concat(body).ToArray();

            if (!message.Remote.PublicKey.Verify(messageForVerify.ToByteArray(), signature))
            {
                throw new InvalidMessageException("The message signature is invalid", message);
            }

            if (!reply)
            {
                message.Identity = raw[0].Buffer.ToArray();
            }

            return message;
        }

        // TODO: reply is not required anymore.
        public static Message Deserialize(
            byte[] bytes,
            AppProtocolVersion localVersion,
            IImmutableSet<PublicKey> trustedAppProtocolVersionSigners,
            DifferentAppProtocolVersionEncountered differentAppProtocolVersionEncountered,
            TimeSpan? lifetime)
        {
            using var stream = new MemoryStream(bytes);
            var buffer = new byte[sizeof(int)];
            stream.Read(buffer, 0, sizeof(int));
            int frameCount = BitConverter.ToInt32(buffer, 0);
            var frames = new List<NetMQFrame>();
            for (var i = 0; i < frameCount; i++)
            {
                buffer = new byte[sizeof(int)];
                stream.Read(buffer, 0, sizeof(int));
                int frameSize = BitConverter.ToInt32(buffer, 0);
                buffer = new byte[frameSize];
                stream.Read(buffer, 0, frameSize);
                frames.Add(new NetMQFrame(buffer));
            }

            NetMQMessage message = new NetMQMessage(frames);
            return Parse(
                message,
                false,
                localVersion,
                trustedAppProtocolVersionSigners,
                differentAppProtocolVersionEncountered,
                lifetime);
        }

        /// <summary>
        /// Casts the message to <see cref="NetMQMessage"/> with given <paramref name="key"/>,
        /// <paramref name="peer"/> and <paramref name="version"/>.
        /// </summary>
        /// <param name="key">A <see cref="PrivateKey"/> to sign message.</param>
        /// <param name="peer"><see cref="Peer"/>-typed representation of the
        /// sender's transport layer.
        /// <seealso cref="ITransport.AsPeer"/></param>
        /// <param name="timestamp">The <see cref="DateTimeOffset"/> of the message is created.
        /// </param>
        /// <param name="version"><see cref="AppProtocolVersion"/>-typed version of the
        /// transport layer.</param>
        /// <returns>A <see cref="NetMQMessage"/> containing the signed <see cref="Message"/>.
        /// </returns>
        /// <exception cref="ArgumentNullException">Thrown when <paramref name="peer"/> is
        /// <c>null</c>.</exception>
        public NetMQMessage ToNetMQMessage(
            PrivateKey key,
            Peer peer,
            DateTimeOffset timestamp,
            AppProtocolVersion version)
        {
            if (peer is null)
            {
                throw new ArgumentNullException(nameof(peer));
            }

            var message = new NetMQMessage();

            // Write body (by concrete class)
            foreach (NetMQFrame frame in DataFrames)
            {
                message.Append(frame);
            }

            // Write headers. (inverse order)
            message.Push(timestamp.Ticks);
            message.Push(SerializePeer(peer));
            message.Push((byte)Type);
            message.Push(version.Token);

            // Make and insert signature
            byte[] signature = key.Sign(message.ToByteArray());
            List<NetMQFrame> frames = message.ToList();
            frames.Insert((int)MessageFrame.Sign, new NetMQFrame(signature));
            message = new NetMQMessage(frames);

            if (Identity is byte[] to)
            {
                message.Push(to);
            }

            return message;
        }

        public byte[] Serialize(
            PrivateKey key,
            Peer peer,
            DateTimeOffset timestamp,
            AppProtocolVersion version)
        {
            NetMQMessage netMqMessage = ToNetMQMessage(key, peer, timestamp, version);
            using var stream = new MemoryStream();
            stream.Write(BitConverter.GetBytes(netMqMessage.FrameCount), 0, sizeof(int));
            foreach (var frame in netMqMessage)
            {
                stream.Write(BitConverter.GetBytes(frame.BufferSize), 0, sizeof(int));
                stream.Write(frame.ToByteArray(), 0, frame.BufferSize);
            }

            return stream.ToArray();
        }

        protected static Peer DeserializePeer(byte[] bytes)
        {
            var formatter = new BinaryFormatter();
            using MemoryStream stream = new MemoryStream(bytes);
            return (Peer)formatter.Deserialize(stream);
        }

        protected byte[] SerializePeer(Peer peer)
        {
            var formatter = new BinaryFormatter();
            using MemoryStream stream = new MemoryStream();
            formatter.Serialize(stream, peer);
            return stream.ToArray();
        }

        private static bool IsAppProtocolVersionValid(
            Peer remotePeer,
            AppProtocolVersion localVersion,
            AppProtocolVersion remoteVersion,
            IImmutableSet<PublicKey> trustedAppProtocolVersionSigners,
            DifferentAppProtocolVersionEncountered differentAppProtocolVersionEncountered)
        {
            if (remoteVersion.Equals(localVersion))
            {
                return true;
            }

            if (!(trustedAppProtocolVersionSigners is null) &&
                !trustedAppProtocolVersionSigners.Any(remoteVersion.Verify))
            {
                return false;
            }

            if (differentAppProtocolVersionEncountered is null)
            {
                return false;
            }

            return differentAppProtocolVersionEncountered(remotePeer, remoteVersion, localVersion);
        }
    }
}
