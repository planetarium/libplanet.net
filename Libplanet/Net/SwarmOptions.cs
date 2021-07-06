using System;
using System.Collections.Immutable;
using System.Threading;
using Libplanet.Blockchain;
using Libplanet.Blocks;
using Libplanet.Net.Messages;
using Libplanet.Net.Protocols;
using Libplanet.Net.Transports;
using Libplanet.Tx;

namespace Libplanet.Net
{
    public class SwarmOptions
    {
        /// <summary>
        /// <c>Enum</c> represents the type of the <see cref="ITransport"/>.
        /// </summary>
        public enum TransportType : byte
        {
            /// <summary>
            /// NetMQ based transport.
            /// </summary>
            NetMQTransport = 0x01,

            /// <summary>
            /// TCP based transport.
            /// </summary>
            TcpTransport = 0x02,
        }

        /// <summary>
        /// The maximum timeout used in <see cref="Swarm{T}"/>.
        /// </summary>
        public TimeSpan MaxTimeout { get; set; } = TimeSpan.FromSeconds(150);

        /// <summary>
        /// The base timeout used to receive the block hashes from other peers.
        /// </summary>
        public TimeSpan BlockHashRecvTimeout { get; set; } = TimeSpan.FromSeconds(30);

        /// <summary>
        /// The base timeout used to receive <see cref="Block{T}"/> from other peers.
        /// </summary>
        public TimeSpan BlockRecvTimeout { get; set; } = TimeSpan.FromSeconds(15);

        /// <summary>
        /// The base timeout used to receive <see cref="Transaction{T}"/> from other peers.
        /// </summary>
        public TimeSpan TxRecvTimeout { get; set; } = TimeSpan.FromSeconds(3);

        /// <summary>
        /// The timeout used to receive recent states from other peers.
        /// </summary>
        public TimeSpan RecentStateRecvTimeout { get; set; } = TimeSpan.FromSeconds(90);

        /// <summary>
        /// The timeout used to block download in preloading.
        /// </summary>
        public TimeSpan BlockDownloadTimeout { get; set; } = Timeout.InfiniteTimeSpan;

        /// <summary>
        /// The lifespan of block demand.
        /// </summary>
        public TimeSpan BlockDemandLifespan { get; set; } = TimeSpan.FromMinutes(1);

        /// <summary>
        /// The lifespan of <see cref="Message"/>.
        /// </summary>
        public TimeSpan? MessageLifespan { get; set; } = null;

        /// <summary>
        /// The frequency of <see cref="IProtocol.RefreshTableAsync" />.
        /// </summary>
        public TimeSpan RefreshPeriod { get; set; } = TimeSpan.FromSeconds(10);

        /// <summary>
        /// The lifespan of <see cref="Peer"/> in routing table.
        /// <seealso cref="IProtocol.RefreshTableAsync" />
        /// </summary>
        public TimeSpan RefreshLifespan { get; set; } = TimeSpan.FromSeconds(60);

        /// <summary>
        /// The list of <see cref="Peer"/>s to keep in routing table permanently.
        /// The <see cref="Peer"/>s in the list won't be removed in any cases.
        /// </summary>
        public IImmutableSet<BoundPeer> StaticPeers { get; set; } =
            ImmutableHashSet<BoundPeer>.Empty;

        /// <summary>
        /// The threshold for detecting branchpoint when block synchronization.
        /// If the branch point is outside threshold from the <see cref="BlockChain{T}.Tip" />,
        /// using an approximated value.
        /// </summary>
        public int BranchpointThreshold { get; set; } = 10;

        /// <summary>
        /// The type of <see cref="ITransport"/> used in <see cref="Swarm{T}"/>.
        /// </summary>
        public TransportType Type { get; set; } = TransportType.TcpTransport;
    }
}
