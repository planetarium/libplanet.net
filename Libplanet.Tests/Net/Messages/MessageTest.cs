using System;
using System.Collections.Immutable;
using System.Linq;
using System.Net;
using System.Security.Cryptography;
using Libplanet.Crypto;
using Libplanet.Net;
using Libplanet.Net.Messages;
using Libplanet.Tests.Common.Action;
using NetMQ;
using Xunit;

namespace Libplanet.Tests.Net.Messages
{
    public class MessageTest
    {
        [Fact]
        public void DifferentAppProtocolVersionWithSameStructure()
        {
            var privateKey = new PrivateKey();
            var peer = new Peer(privateKey.PublicKey);
            var validAppProtocolVersion = new AppProtocolVersion(
                1,
                new Bencodex.Types.Integer(0),
                ImmutableArray<byte>.Empty,
                default(Address));
            var invalidAppProtocolVersion = new AppProtocolVersion(
                2,
                new Bencodex.Types.Integer(0),
                ImmutableArray<byte>.Empty,
                default(Address));
            var message = new Ping();
            var netMQMessage = message.ToNetMQMessage(
                privateKey,
                peer,
                DateTimeOffset.UtcNow,
                validAppProtocolVersion);

            Assert.Throws<DifferentAppProtocolVersionException>(() =>
                Message.Parse(
                    netMQMessage,
                    true,
                    invalidAppProtocolVersion,
                    ImmutableHashSet<PublicKey>.Empty,
                    null,
                    null));
        }

        [Fact]
        public void DifferentAppProtocolVersionWithDifferentStructure()
        {
            PrivateKey signer = new PrivateKey();
            var validAppProtocolVersion = new AppProtocolVersion(
                1,
                new Bencodex.Types.Integer(0),
                ImmutableArray<byte>.Empty,
                signer.PublicKey.ToAddress());
            var invalidAppProtocolVersion = new AppProtocolVersion(
                2,
                new Bencodex.Types.Integer(0),
                ImmutableArray<byte>.Empty,
                default(Address));
            var netMQMessage = new NetMQMessage();
            netMQMessage.Push(validAppProtocolVersion.Token);

            Assert.Throws<DifferentAppProtocolVersionException>(() =>
                Message.Parse(
                    netMQMessage,
                    true,
                    invalidAppProtocolVersion,
                    ImmutableHashSet<PublicKey>.Empty,
                    null,
                    null));
        }

        [Fact]
        public void InvalidTimestamp()
        {
            var privateKey = new PrivateKey();
            var peer = new Peer(privateKey.PublicKey);
            var futureOffset = DateTimeOffset.MaxValue;
            var pastOffset = DateTimeOffset.MinValue;
            var appProtocolVersion = new AppProtocolVersion(
                1,
                new Bencodex.Types.Integer(0),
                ImmutableArray<byte>.Empty,
                default(Address));
            var message = new Ping();
            NetMQMessage futureRaw =
                message.ToNetMQMessage(privateKey, peer, futureOffset, appProtocolVersion);
            // Messages from the future throws InvalidTimestampException.
            Assert.Throws<InvalidTimestampException>(() =>
                Message.Parse(
                    futureRaw,
                    true,
                    appProtocolVersion,
                    ImmutableHashSet<PublicKey>.Empty,
                    null,
                    TimeSpan.FromSeconds(1)));
            NetMQMessage pastRaw =
                message.ToNetMQMessage(privateKey, peer, pastOffset, appProtocolVersion);
            // Messages from the far past throws InvalidTimestampException.
            Assert.Throws<InvalidTimestampException>(() =>
                Message.Parse(
                    pastRaw,
                    true,
                    appProtocolVersion,
                    ImmutableHashSet<PublicKey>.Empty,
                    null,
                    TimeSpan.FromSeconds(1)));
        }

        [Fact]
        public void Parse()
        {
            var privateKey = new PrivateKey();
            var peer = new Peer(privateKey.PublicKey);
            var dateTimeOffset = DateTimeOffset.UtcNow;
            var appProtocolVersion = new AppProtocolVersion(
                1,
                new Bencodex.Types.Integer(0),
                ImmutableArray<byte>.Empty,
                default(Address));
            var message = new Ping();
            NetMQMessage raw =
                message.ToNetMQMessage(privateKey, peer, dateTimeOffset, appProtocolVersion);
            var parsed = Message.Parse(raw, true, appProtocolVersion, null, null, null);
            Assert.Equal(peer, parsed.Remote);
            Assert.Equal(appProtocolVersion, parsed.Version);
            Assert.Equal(dateTimeOffset, parsed.Timestamp);
        }

        [Fact]
        public void BlockHeaderMessage()
        {
            var privateKey = new PrivateKey();
            var peer = new Peer(privateKey.PublicKey);
            var appProtocolVersion = new AppProtocolVersion(
                1,
                new Bencodex.Types.Integer(0),
                ImmutableArray<byte>.Empty,
                default(Address));
            var dateTimeOffset = DateTimeOffset.UtcNow;
            var genesis = TestUtils.MineGenesis<DumbAction>(_ => HashAlgorithmType.Of<SHA256>());
            var message = new BlockHeaderMessage(genesis.Hash, genesis.Header);
            NetMQMessage raw =
                message.ToNetMQMessage(privateKey, peer, dateTimeOffset, appProtocolVersion);
            var parsed = Message.Parse(raw, true, appProtocolVersion, null, null, null);
            Assert.Equal(peer, parsed.Remote);
        }

        [Fact]
        public void UseInvalidSignature()
        {
            // Victim
            var privateKey = new PrivateKey();
            var peer = new Peer(privateKey.PublicKey, new IPAddress(1024L));
            var dateTimeOffset = DateTimeOffset.UtcNow;
            var validAppProtocolVersion = new AppProtocolVersion(
                1,
                new Bencodex.Types.Integer(0),
                ImmutableArray<byte>.Empty,
                default(Address));
            var ping = new Ping();
            var netMqMessage = ping
                .ToNetMQMessage(privateKey, peer, dateTimeOffset, validAppProtocolVersion)
                .ToArray();

            // Attacker
            var fakePeer = new Peer(privateKey.PublicKey, new IPAddress(2048L));
            var fakeMessage = ping
                .ToNetMQMessage(
                    privateKey,
                    fakePeer,
                    dateTimeOffset,
                    validAppProtocolVersion)
                .ToArray();

            var frames = new NetMQMessage();
            frames.Push(netMqMessage[4]);
            frames.Push(netMqMessage[3]);
            frames.Push(fakeMessage[2]);
            frames.Push(netMqMessage[1]);
            frames.Push(netMqMessage[0]);

            Assert.Throws<InvalidMessageException>(() =>
            {
                Message.Parse(
                    frames,
                    true,
                    validAppProtocolVersion,
                    ImmutableHashSet<PublicKey>.Empty,
                    null,
                    TimeSpan.FromSeconds(5));
            });
        }

        [Fact]
        public void Serialize()
        {
            var privateKey = new PrivateKey();
            var peer = new Peer(privateKey.PublicKey);
            var dateTimeOffset = DateTimeOffset.UtcNow;
            var appProtocolVersion = new AppProtocolVersion(
                1,
                new Bencodex.Types.Integer(0),
                ImmutableArray<byte>.Empty,
                default(Address));
            var message = new Ping();
            var id = Guid.NewGuid();
            message.Identity = id.ToByteArray();
            byte[] serialized =
                message.Serialize(privateKey, peer, dateTimeOffset, appProtocolVersion);
            Message deserialized = Message.Deserialize(
                serialized,
                appProtocolVersion,
                null,
                null,
                null);
            Assert.Equal(peer, deserialized.Remote);
            Assert.Equal(appProtocolVersion, deserialized.Version);
            Assert.Equal(dateTimeOffset, deserialized.Timestamp);
            Assert.Equal(id.ToByteArray(), deserialized.Identity);
        }
    }
}
