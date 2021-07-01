using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Threading;
using Libplanet.Crypto;
using Libplanet.Net;
using Libplanet.Net.Protocols;
using Serilog;
using Serilog.Core;
using Xunit;
using Xunit.Abstractions;

namespace Libplanet.Tests.Net.Protocols
{
    public class RoutingTableTest
    {
        private const int BucketSize = 16;
        private const int TableSize = Address.Size * sizeof(byte) * 8;

        private static readonly PrivateKey VersionSigner = new PrivateKey();
        private static readonly AppProtocolVersion AppProtocolVer =
            AppProtocolVersion.Sign(VersionSigner, 1);

        public RoutingTableTest(ITestOutputHelper output)
        {
            const string outputTemplate =
                "{Timestamp:HH:mm:ss:ffffff} - {Message}";
            Log.Logger = new LoggerConfiguration()
                .MinimumLevel.Verbose()
                .WriteTo.TestOutput(output, outputTemplate: outputTemplate)
                .CreateLogger()
                .ForContext<RoutingTableTest>();
        }

        [Fact]
        public void BucketTest()
        {
            var bucket = new KBucket(4, new System.Random(), Logger.None);
            var peer1 = new BoundPeer(
                new PrivateKey().PublicKey,
                new DnsEndPoint("0.0.0.0", 1234));
            var peer2 = new BoundPeer(
                new PrivateKey().PublicKey,
                new DnsEndPoint("0.0.0.0", 1234));
            var peer3 = new BoundPeer(
                new PrivateKey().PublicKey,
                new DnsEndPoint("0.0.0.0", 1234));
            var peer4 = new BoundPeer(
                new PrivateKey().PublicKey,
                new DnsEndPoint("0.0.0.0", 1234));
            var peer5 = new BoundPeer(
                new PrivateKey().PublicKey,
                new DnsEndPoint("0.0.0.0", 1234));

            Assert.Empty(bucket.Peers);
            Assert.True(bucket.IsEmpty());
            bucket.AddPeer(peer1, DateTimeOffset.UtcNow);
            Assert.True(bucket.Contains(peer1));
            Assert.False(bucket.Contains(peer2));
            Assert.False(bucket.IsEmpty());
            Assert.False(bucket.IsFull());
            // This sleep statement is used to distinguish updated time of followings.
            Thread.Sleep(100);
            bucket.AddPeer(peer2, DateTimeOffset.UtcNow);
            Thread.Sleep(100);
            Assert.Contains(
                bucket.GetRandomPeer(null),
                new[] { peer1, peer2 }
            );
            Assert.Contains(
                bucket.GetRandomPeer(peer1.Address),
                new[] { peer2 }
            );
            bucket.AddPeer(peer3, DateTimeOffset.UtcNow);
            Thread.Sleep(100);
            bucket.AddPeer(peer4, DateTimeOffset.UtcNow);
            Assert.True(bucket.IsFull());
            Assert.Equal(
                bucket.Peers.ToHashSet(),
                new HashSet<BoundPeer> { peer1, peer2, peer3, peer4 }
            );
            Assert.Contains(
                bucket.GetRandomPeer(null),
                new[] { peer1, peer2, peer3, peer4 }
            );
            Thread.Sleep(100);
            bucket.AddPeer(peer5, DateTimeOffset.UtcNow);
            Assert.Equal(
                bucket.Peers.ToHashSet(),
                new HashSet<BoundPeer> { peer1, peer2, peer3, peer4 }
            );
            Assert.False(bucket.Contains(peer5));
            Assert.Equal(peer4, bucket.Head.Peer);
            Assert.Equal(peer1, bucket.Tail.Peer);
            Thread.Sleep(100);
            bucket.AddPeer(peer1, DateTimeOffset.UtcNow);
            Assert.Equal(peer1, bucket.Head.Peer);
            Assert.Equal(peer2, bucket.Tail.Peer);

            Assert.False(bucket.RemovePeer(peer5));
            Assert.True(bucket.RemovePeer(peer1));
            Assert.DoesNotContain(peer1, bucket.Peers);
            Assert.Equal(3, bucket.Peers.Count());

            bucket.Clear();
            Assert.True(bucket.IsEmpty());
        }

        [Fact]
        public void AddSelf()
        {
            var pubKey = new PrivateKey().PublicKey;
            var table = new RoutingTable(pubKey.ToAddress());
            var peer = new BoundPeer(pubKey, new DnsEndPoint("0.0.0.0", 1234));
            Assert.Throws<ArgumentException>(() => table.AddPeer(peer));
        }

        [Fact]
        public void AddNull()
        {
            var pubKey = new PrivateKey().PublicKey;
            var table = new RoutingTable(pubKey.ToAddress());
            Assert.Throws<ArgumentNullException>(() => table.AddPeer(null));
        }

        [Fact]
        public void AddPeer()
        {
            var pubKey0 = new PrivateKey().PublicKey;
            var pubKey1 = new PrivateKey().PublicKey;
            var pubKey2 = new PrivateKey().PublicKey;
            var pubKey3 = new PrivateKey().PublicKey;
            var table = new RoutingTable(pubKey0.ToAddress(), 1, 2);
            var peer1 = new BoundPeer(pubKey1, new DnsEndPoint("0.0.0.0", 1234));
            var peer2 = new BoundPeer(pubKey2, new DnsEndPoint("0.0.0.0", 1234));
            var peer3 = new BoundPeer(pubKey3, new DnsEndPoint("0.0.0.0", 1234));
            table.AddPeer(peer1);
            table.AddPeer(peer2);
            table.AddPeer(peer3);
            table.AddPeer(peer1);
            table.AddPeer(peer3);
            Assert.Equal(
                new HashSet<BoundPeer> { peer1, peer2 },
                table.Peers.ToHashSet()
            );
        }

        [Fact]
        public void RemovePeer()
        {
            var pubKey1 = new PrivateKey().PublicKey;
            var pubKey2 = new PrivateKey().PublicKey;
            var table = new RoutingTable(pubKey1.ToAddress(), 1, 2);
            var peer1 = new BoundPeer(pubKey1, new DnsEndPoint("0.0.0.0", 1234));
            var peer2 = new BoundPeer(pubKey2, new DnsEndPoint("0.0.0.0", 1234));

            Assert.Throws<ArgumentException>(() => table.RemovePeer(peer1));
            Assert.Throws<ArgumentNullException>(() => table.RemovePeer(null));

            bool ret = table.RemovePeer(peer2);
            Assert.False(ret);
            table.AddPeer(peer2);
            ret = table.RemovePeer(peer2);
            Assert.True(ret);
        }

        [Fact]
        public void Generate()
        {
            var table = new RoutingTable(
                new Address(
                    new byte[]
                    {
                        0xaa, 0xba, 0xf4, 0x9a, 0x08, 0x49, 0xaf, 0xa2, 0x43, 0x0b, 0x8e, 0x2b,
                        0xf7, 0xaf, 0x9c, 0x48, 0x05, 0xb7, 0x63, 0xb9,
                    }));
            const int targetBucket = 5;
            int count = 0;
            PublicKey publicKey;
            do
            {
                count++;
                publicKey = new PrivateKey().PublicKey;
            }
            while (table.GetBucketIndexOf(publicKey.ToAddress()) != targetBucket);

            Log.Debug(
                "Found public key of bucket index {Index} in {Count} tries: {Key}",
                table.GetBucketIndexOf(publicKey.ToAddress()),
                count,
                ByteArrayToString(publicKey.Format(true)));
            Assert.Equal(targetBucket, table.GetBucketIndexOf(publicKey.ToAddress()));
        }

        [Fact]
        public void PeersToBroadcast()
        {
            var (publicKey, publicKeys) = GeneratePeersDifferentBuckets();

            var table = new RoutingTable(publicKey.ToAddress());
            var peers = publicKeys
                .Select(pk => new BoundPeer(pk, new DnsEndPoint("0.0.0.0", 1234)))
                .ToArray();
            Assert.Equal(10, peers.Length);
            for (var i = 0; i < peers.Length; i++)
            {
                var peer = peers[i];
                table.AddPeer(peer);
                Assert.Equal(i / 2, table.GetBucketIndexOf(peer.Address));
            }

            var broadcastCandidate = table.PeersToBroadcast(null, 0);
            Assert.Equal(5, broadcastCandidate.Count);
            Assert.Equal(
                new HashSet<int> { 0, 1, 2, 3, 4 },
                broadcastCandidate.Select(peer => table.GetBucketIndexOf(peer.Address))
                    .ToHashSet());

            broadcastCandidate = table.PeersToBroadcast(null, 10);
            Assert.Equal(10, broadcastCandidate.Count);
            Assert.Equal(peers.ToHashSet(), broadcastCandidate.ToHashSet());
        }

        [Fact]
        public void PeersToRefresh()
        {
            var (publicKey, publicKeys) = GeneratePeersDifferentBuckets();
            var table = new RoutingTable(publicKey.ToAddress());
            int peerCount = publicKeys.Length;
            BoundPeer[] peers = publicKeys
                .Select(
                    key => new BoundPeer(
                        key,
                        new DnsEndPoint("0.0.0.0", 1234)))
                .ToArray();
            for (var i = 0; i < peerCount; i++)
            {
                table.AddPeer(
                    peers[i],
                    DateTimeOffset.UtcNow - (i % 2 == 0 ? TimeSpan.Zero : TimeSpan.FromMinutes(2)));
            }

            Assert.Equal(peerCount, table.Peers.Count);
            Assert.Equal(
                Enumerable
                    .Range(0, peerCount / 2)
                    .Select(i => peers[i * 2 + 1]).ToHashSet(),
                table.PeersToRefresh(TimeSpan.FromMinutes(1)).ToHashSet());
        }

        [Fact]
        public void PeersToRefreshInSingleBucket()
        {
            var publicKey = new PrivateKey().PublicKey;
            var table = new RoutingTable(publicKey.ToAddress(), 1);
            const int peerCount = 10;
            BoundPeer[] peers = Enumerable.Range(0, peerCount)
                .Select(
                    i => new BoundPeer(
                        new PrivateKey().PublicKey,
                        new DnsEndPoint("0.0.0.0", 1000 + i)))
                .ToArray();
            for (int i = 0; i < peerCount; i++)
            {
                table.AddPeer(
                    peers[i],
                    DateTimeOffset.UtcNow - TimeSpan.FromMinutes(2) + TimeSpan.FromSeconds(i));
            }

            Assert.Equal(peerCount, table.Peers.Count);
            for (int i = 0; i < peerCount; i++)
            {
                Assert.Equal(peers[i], table.PeersToRefresh(TimeSpan.FromMinutes(1)).First());
                table.AddPeer(peers[i]);
            }

            Assert.Empty(table.PeersToRefresh(TimeSpan.FromMinutes(1)));
        }

        private (PublicKey, PublicKey[]) GeneratePeersDifferentBuckets()
        {
            var publicKey = new PublicKey(
                new byte[]
                {
                    0x03, 0x1d, 0xf3, 0x53, 0x4d, 0x8d, 0xee, 0x5d, 0x35, 0xd2, 0x6c, 0xf4, 0x1c,
                    0x52, 0x62, 0x93, 0x26, 0xfc, 0x20, 0xbf, 0x96, 0xd4, 0x9b, 0xdd, 0x6c, 0x45,
                    0x96, 0xdb, 0x49, 0x18, 0x96, 0xda, 0xf7,
                });
            var publicKeys = new[]
            {
                // Peer 0 is in bucket 0
                new PublicKey(
                    new byte[]
                    {
                        0x02, 0xac, 0x9d, 0x71, 0x9f, 0x8d, 0xd7, 0xfb, 0x8d, 0x32, 0xa6, 0x1f,
                        0x95, 0xb3, 0x41, 0xe2, 0x32, 0xed, 0xf7, 0xca, 0xe3, 0x30, 0xc7, 0x6b,
                        0xbf, 0xc3, 0xb9, 0x88, 0xef, 0x66, 0x4d, 0x36, 0xb7,
                    }),
                // Peer 1 is in bucket 0
                new PublicKey(
                    new byte[]
                    {
                        0x03, 0xa6, 0xa0, 0xea, 0xbb, 0x9a, 0x02, 0x5e, 0x20, 0xb0, 0x89, 0x0a,
                        0x0d, 0x5b, 0xfd, 0xf2, 0x16, 0x8d, 0x3a, 0xf9, 0x6a, 0xc8, 0xe1, 0x9d,
                        0x83, 0x26, 0x5f, 0x75, 0xce, 0x98, 0xa2, 0xda, 0xde,
                    }),
                // Peer 2 is in bucket 1
                new PublicKey(
                    new byte[]
                    {
                        0x02, 0x24, 0x97, 0x35, 0x83, 0xa3, 0x6a, 0x2b, 0x80, 0xfd, 0xb7, 0xae,
                        0xa7, 0xe3, 0x7f, 0xc5, 0xd3, 0xcd, 0x97, 0xaa, 0xcc, 0x6a, 0x83, 0xf5,
                        0x0e, 0xff, 0x3f, 0x49, 0x9d, 0x6e, 0xdc, 0x0b, 0x45,
                    }),
                // Peer 3 is in bucket 1
                new PublicKey(
                    new byte[]
                    {
                        0x02, 0xbd, 0xa7, 0x70, 0xf7, 0xa0, 0x60, 0x81, 0x35, 0xb4, 0x7e, 0x1f,
                        0x07, 0xde, 0x28, 0x02, 0xd2, 0xa2, 0xec, 0x61, 0xae, 0x1e, 0x93, 0xf9,
                        0x41, 0x6b, 0xb0, 0x65, 0xa6, 0x22, 0xb6, 0x87, 0xa6,
                    }),
                // Peer 4 is in bucket 2
                new PublicKey(
                    new byte[]
                    {
                        0x02, 0x73, 0x47, 0x2f, 0xb2, 0x8a, 0x73, 0xfe, 0x14, 0xa3, 0xec, 0x59,
                        0x8e, 0x73, 0x90, 0x34, 0x0b, 0xac, 0xf5, 0xd8, 0x3c, 0x7f, 0x4b, 0x22,
                        0x16, 0x5a, 0x39, 0x5d, 0x0b, 0x2f, 0xd9, 0xc7, 0x21,
                    }),
                // Peer 5 is in bucket 2
                new PublicKey(
                    new byte[]
                    {
                        0x03, 0x5f, 0x73, 0x5b, 0x3e, 0xa5, 0x26, 0xd6, 0xaf, 0x53, 0xd1, 0x10,
                        0x2a, 0x5f, 0xe2, 0xb3, 0xcc, 0x95, 0xc7, 0xca, 0xae, 0x41, 0xdd, 0x58,
                        0xe1, 0xa3, 0x5f, 0x1b, 0x84, 0x59, 0xff, 0x8a, 0xda,
                    }),
                // Peer 6 is in bucket 3
                new PublicKey(
                    new byte[]
                    {
                        0x03, 0x65, 0xbd, 0x28, 0xce, 0xeb, 0x8b, 0x4a, 0x1e, 0x56, 0x36, 0x26,
                        0x0f, 0x36, 0xdd, 0xd1, 0x9f, 0x14, 0x0e, 0x8e, 0x1e, 0x48, 0x20, 0x1c,
                        0xdd, 0x57, 0xde, 0x71, 0x52, 0x26, 0x6e, 0xa9, 0x5b,
                    }),
                // Peer 7 is in bucket 3
                new PublicKey(
                    new byte[]
                    {
                        0x02, 0x41, 0x04, 0x9c, 0xcd, 0x1e, 0xcb, 0x8a, 0xc2, 0xbe, 0x2c, 0x98,
                        0xdb, 0x62, 0x8e, 0x9f, 0xf2, 0x9b, 0x9c, 0x3d, 0x2d, 0x8a, 0x3d, 0x63,
                        0xf2, 0xd1, 0xb7, 0xa6, 0xc3, 0xd3, 0x0c, 0x7d, 0x8f,
                    }),
                // Peer 8 is in bucket 4
                new PublicKey(
                    new byte[]
                    {
                        0x03, 0x38, 0x4e, 0xef, 0xfb, 0x76, 0xca, 0xf5, 0xe9, 0x5f, 0xcc, 0xf1,
                        0x54, 0xb4, 0xaf, 0x16, 0x85, 0xd6, 0x48, 0xa7, 0xc8, 0x7d, 0x44, 0x74,
                        0xff, 0xfc, 0xf1, 0x5d, 0x92, 0xa6, 0xe9, 0x79, 0x6e,
                    }),
                // Peer 9 is in bucket 4
                new PublicKey(
                    new byte[]
                    {
                        0x02, 0x4c, 0x11, 0x05, 0x7c, 0x7e, 0x18, 0xd6, 0x04, 0xd4, 0x5b, 0x01,
                        0xdb, 0xba, 0x6c, 0x03, 0xf0, 0x6c, 0x95, 0x45, 0xa9, 0x98, 0x50, 0xbc,
                        0x8e, 0x9b, 0x7c, 0x65, 0xbe, 0x41, 0x97, 0xce, 0x5c,
                    }),
            };

            return (publicKey, publicKeys);
        }

        private string ByteArrayToString(byte[] bytes)
        {
            var str = BitConverter.ToString(bytes);
            str = "0x" + str.Replace("-", ", 0x").ToLower();

            return str + ",";
        }
    }
}
