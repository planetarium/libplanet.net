using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Libplanet.Net.Messages;
using Libplanet.Net.Transports;
using Serilog;
using Random = System.Random;

namespace Libplanet.Net.Protocols
{
    /// <summary>
    /// A Kademlia based peer discovery protocol.
    /// </summary>
    public class KademliaProtocol : IProtocol
    {
        private readonly TimeSpan _requestTimeout;
        private readonly ITransport _transport;
        private readonly Address _address;

        private readonly Random _random;
        private readonly RoutingTable _table;
        private readonly int _findConcurrency;

        private readonly ILogger _logger;

        /// <summary>
        /// Creates a <see cref="KademliaProtocol"/> instance.
        /// </summary>
        /// <param name="table">
        /// The <see cref="RoutingTable"/> where <see cref="Peer"/>s are stored.</param>
        /// <param name="transport"><see cref="ITransport"/> to process messages.</param>
        /// <param name="address">The <see cref="Address"/> of the <see cref="Peer"/>
        /// to be the reference point.</param>
        /// <param name="findConcurrency">The number of concurrency in peer discovery.</param>
        /// <param name="requestTimeout">
        /// A timeout of waiting for the reply of messages.
        /// If it's omitted or <c>null</c> is given, will automatically be set to 5 seconds.
        /// </param>
        public KademliaProtocol(
            RoutingTable table,
            ITransport transport,
            Address address,
            int findConcurrency = Kademlia.FindConcurrency,
            TimeSpan? requestTimeout = null)
        {
            _transport = transport;
            _logger = Log.ForContext<KademliaProtocol>();

            _address = address;
            _random = new System.Random();
            _findConcurrency = findConcurrency;
            _table = table;
            _requestTimeout =
                requestTimeout ??
                TimeSpan.FromMilliseconds(5000);
            _transport.ProcessMessageHandler.Register(ProcessMessageHandler);
        }

        /// <inheritdoc />
        // FIXME: Currently bootstrap is done until it finds closest peer, but it should halt
        // when found neighbor's count is reached 2*k.
        public async Task BootstrapAsync(
            IEnumerable<BoundPeer> bootstrapPeers,
            TimeSpan? pingSeedTimeout,
            TimeSpan? findNeighborsTimeout,
            int depth,
            CancellationToken cancellationToken)
        {
            if (bootstrapPeers is null)
            {
                throw new ArgumentNullException(nameof(bootstrapPeers));
            }

            var findPeerTasks = new List<Task>();
            var history = new ConcurrentBag<BoundPeer>();
            var dialHistory = new ConcurrentBag<BoundPeer>();

            foreach (BoundPeer peer in bootstrapPeers.Where(peer => !peer.Address.Equals(_address)))
            {
                // Guarantees at least one connection (seed peer)
                try
                {
                    await PingAsync(peer, pingSeedTimeout, cancellationToken);
                    findPeerTasks.Add(
                        FindPeerAsync(
                            history,
                            dialHistory,
                            _address,
                            peer,
                            depth,
                            findNeighborsTimeout,
                            cancellationToken));
                }
                catch (DifferentAppProtocolVersionException)
                {
                    _logger.Error("Version is different from seed peer.");
                }
                catch (PingTimeoutException)
                {
                    _logger.Warning("A timeout exception occurred connecting to seed peer.");
                    RemovePeer(peer);
                }
                catch (Exception e)
                {
                    _logger.Error(
                        e,
                        "An unexpected exception occurred connecting to seed peer. {Exception}",
                        e);
                }
            }

            if (!_table.Peers.Any())
            {
                throw new PeerDiscoveryException("All seeds are unreachable.");
            }

            if (findPeerTasks.Count == 0)
            {
                throw new PeerDiscoveryException("Bootstrap failed.");
            }

            try
            {
                await Task.WhenAll(findPeerTasks);
            }
            catch (Exception e)
            {
                var msg = $"An unexpected exception occurred during {nameof(BootstrapAsync)}()." +
                          " {Exception}";
                _logger.Error(e, msg, e);
                throw;
            }
        }

        /// <inheritdoc />
        public async Task AddPeersAsync(
            IEnumerable<Peer> peers,
            TimeSpan? timeout,
            CancellationToken cancellationToken)
        {
            try
            {
                var tasks = new List<Task>();
                foreach (Peer peer in peers)
                {
                    if (peer is BoundPeer boundPeer)
                    {
                        tasks.Add(PingAsync(
                            boundPeer,
                            timeout: timeout,
                            cancellationToken: cancellationToken));
                    }
                }

                _logger.Verbose("Trying to ping all {PeersNumber} peers.", tasks.Count);
                await Task.WhenAll(tasks);
                _logger.Verbose("Update complete.");
            }
            catch (DifferentAppProtocolVersionException e)
            {
                AppProtocolVersion expected = e.ExpectedVersion, actual = e.ActualVersion;
                _logger.Debug(
                    $"Different version encountered during {nameof(AddPeersAsync)}().\n" +
                    "Expected version: {ExpectedVersion} ({ExpectedVersionExtra}) " +
                    "[{ExpectedSignature}; {ExpectedSigner}]\n" +
                    "Actual version: {ActualVersion} ({ActualVersionExtra}) [{ActualSignature};" +
                    "{ActualSigner}]",
                    expected.Version,
                    expected.Extra,
                    ByteUtil.Hex(expected.Signature),
                    expected.Signer.ToString(),
                    actual.Version,
                    actual.Extra,
                    ByteUtil.Hex(actual.Signature),
                    actual.Signer
                );
            }
            catch (TimeoutException e)
            {
                const string msg =
                    "Timeout occurred during " + nameof(AddPeersAsync) + "() after {Timeout}.";
                _logger.Debug(e, msg, timeout);
                throw;
            }
            catch (TaskCanceledException e)
            {
                const string msg = "Task is cancelled during " + nameof(AddPeersAsync) + "().";
                _logger.Debug(e, msg);
            }
            catch (Exception e)
            {
                const string msg = "Unexpected exception occurred during " +
                                   nameof(AddPeersAsync) + "(): {Exception}";
                _logger.Error(e, msg, e);
                throw;
            }
        }

        /// <inheritdoc />
        public async Task RefreshTableAsync(TimeSpan maxAge, CancellationToken cancellationToken)
        {
            // TODO: Add timeout parameter for this method
            try
            {
                _logger.Verbose("Refreshing table... total peers: {Count}", _table.Peers.Count);
                List<Task> tasks = _table.PeersToRefresh(maxAge)
                    .Select(peer =>
                        ValidateAsync(
                            peer,
                            _requestTimeout,
                            cancellationToken)
                    ).ToList();

                _logger.Verbose("Refresh candidates: {Count}", tasks.Count);

                await Task.WhenAll(tasks);
                cancellationToken.ThrowIfCancellationRequested();
            }
            catch (TimeoutException)
            {
            }
        }

        /// <summary>
        /// Refreshes all peers in routing table.
        /// </summary>
        /// <param name="timeout">A timeout of waiting for the reply of messages.
        /// If <c>null</c> is given, the task never halts by itself
        /// even no any response was given from the the target peer.</param>
        /// <param name="cancellationToken">
        /// A cancellation token used to propagate notification that this
        /// operation should be canceled.</param>
        /// <returns>An awaitable task without value.</returns>
        public async Task CheckAllPeersAsync(TimeSpan? timeout, CancellationToken cancellationToken)
        {
            try
            {
                _logger.Verbose("Start to validate all peers: ({Count})", _table.Peers.Count);
                foreach (var peer in _table.Peers)
                {
                    await ValidateAsync(peer, timeout ?? _requestTimeout, cancellationToken);
                }
            }
            catch (TimeoutException e)
            {
                _logger.Error(e, "Timeout occurred checking some peers: {e}", e);
            }
        }

        /// <inheritdoc />
        public async Task RebuildConnectionAsync(int depth, CancellationToken cancellationToken)
        {
            _logger.Verbose("Rebuilding connection...");
            var buffer = new byte[20];
            var tasks = new List<Task>();
            var history = new ConcurrentBag<BoundPeer>();
            var dialHistory = new ConcurrentBag<BoundPeer>();
            for (int i = 0; i < _findConcurrency; i++)
            {
                _random.NextBytes(buffer);
                tasks.Add(FindPeerAsync(
                    history,
                    dialHistory,
                    new Address(buffer),
                    null,
                    depth,
                    _requestTimeout,
                    cancellationToken));
            }

            tasks.Add(
                FindPeerAsync(
                    history,
                    dialHistory,
                    _address,
                    null,
                    depth,
                    _requestTimeout,
                    cancellationToken));
            try
            {
                await Task.WhenAll(tasks);
            }
            catch (TimeoutException)
            {
            }
        }

        /// <inheritdoc />
        public async Task CheckReplacementCacheAsync(CancellationToken cancellationToken)
        {
            _logger.Verbose("Checking replacement cache.");
            foreach (IEnumerable<BoundPeer> cache in _table.CachesToCheck)
            {
                foreach (BoundPeer replacement in cache)
                {
                    try
                    {
                        _logger.Verbose("Check peer {Peer}.", replacement);

                        _table.RemoveCache(replacement);
                        await PingAsync(replacement, _requestTimeout, cancellationToken);
                    }
                    catch (PingTimeoutException)
                    {
                        _logger.Verbose(
                            "Removed stale peer {Peer} from replacement cache.",
                            replacement);
                    }
                }
            }

            _logger.Verbose("Replacement cache checked.");
        }

        /// <summary>
        /// Use <see cref="FindNeighbors"/> messages to to find a <see cref="BoundPeer"/> with
        /// <see cref="Address"/> of <paramref name="target"/>.
        /// </summary>
        /// <param name="target">The <see cref="Address"/> to find.</param>
        /// <param name="depth">Target depth of recursive operation.</param>
        /// <param name="timeout"><see cref="TimeSpan"/> for waiting reply of
        /// <see cref="FindNeighbors"/>.</param>
        /// <param name="cancellationToken">A cancellation token used to propagate notification
        /// that this operation should be canceled.</param>
        /// <returns>A <see cref="BoundPeer"/> with <see cref="Address"/> of
        /// <paramref name="target"/>.</returns>
        public async Task<BoundPeer> FindSpecificPeerAsync(
            Address target,
            int depth,
            TimeSpan? timeout,
            CancellationToken cancellationToken)
        {
            _logger.Verbose(
                $"{nameof(FindSpecificPeerAsync)}() with {{Target}}. " +
                "(depth: {Depth})",
                target,
                depth);

            if (_table.GetPeer(target) is BoundPeer boundPeer)
            {
                try
                {
                    await PingAsync(boundPeer, _requestTimeout, cancellationToken);
                }
                catch (PingTimeoutException)
                {
                    var msg =
                        "{BoundPeer}, a target peer, is in the routing table does not respond.";
                    _logger.Verbose(msg, boundPeer);
                    RemovePeer(boundPeer);
                    return null;
                }

                _logger.Verbose(
                    "{BoundPeer}, a target peer, is in the routing table.",
                    boundPeer);
                return boundPeer;
            }

            var history = new ConcurrentBag<BoundPeer>();
            var peersToFind = new ConcurrentQueue<Tuple<BoundPeer, int>>();
            foreach (BoundPeer peer in _table.Neighbors(target, _findConcurrency, false))
            {
                peersToFind.Enqueue(new Tuple<BoundPeer, int>(peer, 0));
            }

            while (peersToFind.Any())
            {
                cancellationToken.ThrowIfCancellationRequested();

                if (!peersToFind.TryDequeue(out Tuple<BoundPeer, int> tuple))
                {
                    continue;
                }

                tuple.Deconstruct(out BoundPeer viaPeer, out int curDepth);
                _logger.Debug("ViaPeer: {Peer}, curDepth: {curDepth}", viaPeer, curDepth);
                if (depth != -1 && curDepth >= depth)
                {
                    continue;
                }

                history.Add(viaPeer);
                IEnumerable<BoundPeer> foundPeers =
                    await GetNeighbors(viaPeer, target, timeout, cancellationToken);
                IEnumerable<BoundPeer> filteredPeers = foundPeers
                    .Where(peer =>
                        !history.Contains(peer) &&
                        !peersToFind.Any(t => t.Item1.Equals(peer)) &&
                        !peer.Address.Equals(_address))
                    .Take(_findConcurrency);
                int count = 0;
                foreach (var found in filteredPeers)
                {
                    try
                    {
                        await PingAsync(found, _requestTimeout, cancellationToken);
                        if (found.Address.Equals(target))
                        {
                            return found;
                        }

                        peersToFind.Enqueue(new Tuple<BoundPeer, int>(found, curDepth + 1));

                        if (count++ >= _findConcurrency)
                        {
                            break;
                        }
                    }
                    catch (TaskCanceledException)
                    {
                        throw new TaskCanceledException(
                            $"Task is cancelled during {nameof(FindSpecificPeerAsync)}()");
                    }
                    catch (PingTimeoutException)
                    {
                        // Ignore peer not responding
                    }
                    finally
                    {
                        history.Add(found);
                    }
                }
            }

            return null;
        }

        internal async Task PingAsync(
            BoundPeer target,
            TimeSpan? timeout,
            CancellationToken cancellationToken)
        {
            if (target is null)
            {
                throw new ArgumentNullException(nameof(target));
            }

            if (cancellationToken.IsCancellationRequested)
            {
                return;
            }

            try
            {
                _logger.Verbose("Trying to ping async to {Peer}.", target);
                Message reply = await _transport.SendMessageWithReplyAsync(
                    target,
                    new Ping(),
                    timeout,
                    cancellationToken
                );
                if (!(reply is Pong pong))
                {
                    throw new InvalidMessageException(
                        $"Expected pong, but received {reply}.", reply);
                }

                if (pong.Remote.Address.Equals(_address))
                {
                    throw new InvalidMessageException("Cannot receive pong from self", pong);
                }

                Update(target);
            }
            catch (TimeoutException)
            {
                throw new PingTimeoutException(
                    target,
                    $"Timeout occurred during dial to {target}.");
            }
            catch (InvalidTimestampException)
            {
                throw new PingTimeoutException(
                    target,
                    $"Received Pong from {target} has invalid timestamp.");
            }
            catch (DifferentAppProtocolVersionException)
            {
                _logger.Error(
                    $"Different AppProtocolVersion encountered at {nameof(PingAsync)}().");
                throw;
            }
        }

        private async Task ProcessMessageHandler(Message message)
        {
            switch (message)
            {
                case Ping ping:
                {
                    await ReceivePingAsync(ping);
                    break;
                }

                case FindNeighbors findPeer:
                {
                    await ReceiveFindPeerAsync(findPeer);
                    break;
                }
            }

            // Should we update peer status for non-protocol related messages? (i.e. BlockHashes)
            Update(message?.Remote);
        }

        /// <summary>
        /// Validate peer by send <see cref="Ping"/> to <paramref name="peer"/>. If target peer
        /// does not responds, remove it from the table.
        /// </summary>
        /// <param name="peer">A <see cref="BoundPeer"/> to validate.</param>
        /// <param name="timeout">Timeout for waiting reply of <see cref="Ping"/>.</param>
        /// <param name="cancellationToken">A cancellation token used to propagate notification
        /// that this operation should be canceled.</param>
        /// <returns>An awaitable task without value.</returns>
        /// <exception cref="TimeoutException">
        /// Thrown when validation fails in given <paramref name="timeout"/>.
        /// </exception>
        private async Task ValidateAsync(
            BoundPeer peer,
            TimeSpan timeout,
            CancellationToken cancellationToken = default(CancellationToken))
        {
            try
            {
                _logger.Verbose("Start to validate a peer: {Peer}", peer);
                DateTimeOffset check = DateTimeOffset.UtcNow;
                await PingAsync(peer, timeout, cancellationToken);
                _table.Check(peer, check, DateTimeOffset.UtcNow);
            }
            catch (PingTimeoutException)
            {
                _logger.Verbose("Peer {Peer} is invalid, removing...", peer);
                RemovePeer(peer);
                throw new TimeoutException($"Timeout occurred during {nameof(ValidateAsync)}");
            }
        }

        /// <summary>
        /// Updates routing table when receiving a message. If corresponding bucket
        /// for remote peer is not full, just adds given <paramref name="rawPeer"/>.
        /// Otherwise, checks aliveness of the least recently used (LRU) peer
        /// and determine evict LRU peer or discard given <paramref name="rawPeer"/>.
        /// </summary>
        /// <param name="rawPeer"><see cref="Peer"/> to update.</param>
        /// <exception cref="ArgumentNullException">
        /// Thrown when <paramref name="rawPeer"/> is <c>null</c>.
        /// </exception>
        private void Update(Peer rawPeer)
        {
            _logger.Verbose($"Try to {nameof(Update)}() {{Peer}}.", rawPeer);
            if (rawPeer is null)
            {
                throw new ArgumentNullException(nameof(rawPeer));
            }

            if (rawPeer is BoundPeer peer)
            {
                // Don't update peer without endpoint or with different appProtocolVersion.
                _table.AddPeer(peer);
            }
        }

        private void RemovePeer(BoundPeer peer)
        {
            _table.RemovePeer(peer);
        }

        /// <summary>
        /// Send <see cref="FindNeighbors"/> messages to <paramref name="viaPeer"/>
        /// to find <see cref="Peer"/>s near <paramref name="target"/>.
        /// </summary>
        /// <param name="history">The <see cref="Peer"/> that searched.</param>
        /// <param name="dialHistory">The <see cref="Peer"/> that ping was sent.</param>
        /// <param name="target">The <see cref="Address"/> to find.</param>
        /// <param name="viaPeer">The target <see cref="Peer"/> to send <see cref="FindNeighbors"/>
        /// message. If null, selects 3 <see cref="Peer"/>s from <see cref="RoutingTable"/> of
        /// self.</param>
        /// <param name="depth">Target depth of recursive operation.</param>
        /// <param name="timeout"><see cref="TimeSpan"/> for waiting reply of
        /// <see cref="FindNeighbors"/>.</param>
        /// <param name="cancellationToken">A cancellation token used to propagate notification
        /// that this operation should be canceled.</param>
        /// <returns>An awaitable task without value.</returns>
        private async Task FindPeerAsync(
            ConcurrentBag<BoundPeer> history,
            ConcurrentBag<BoundPeer> dialHistory,
            Address target,
            BoundPeer viaPeer,
            int depth,
            TimeSpan? timeout,
            CancellationToken cancellationToken)
        {
            _logger.Verbose(
                $"{nameof(FindPeerAsync)}() with {{Target}} to {{Peer}}. " +
                "(depth: {Depth})",
                target,
                viaPeer,
                depth);
            if (depth == 0)
            {
                return;
            }

            IEnumerable<BoundPeer> found;
            if (viaPeer is null)
            {
                found = await QueryNeighborsAsync(history, target, timeout, cancellationToken);
            }
            else
            {
                found = await GetNeighbors(viaPeer, target, timeout, cancellationToken);
                history.Add(viaPeer);
            }

            // In ethereum's devp2p, GetNeighbors request will exclude peer with address of
            // target. But our implementation contains target itself for FindSpecificPeerAsync(),
            // so it should be excluded in here.
            found = found.Where(peer => !peer.Address.Equals(target));
            await ProcessFoundAsync(
                history,
                dialHistory,
                found,
                target,
                depth,
                timeout,
                cancellationToken);
        }

        private async Task<IEnumerable<BoundPeer>> QueryNeighborsAsync(
            ConcurrentBag<BoundPeer> history,
            Address target,
            TimeSpan? timeout,
            CancellationToken cancellationToken)
        {
            List<BoundPeer> neighbors = _table.Neighbors(target, _table.BucketSize, false).ToList();
            var found = new List<BoundPeer>();
            int count = Math.Min(neighbors.Count, _findConcurrency);
            for (var i = 0; i < count; i++)
            {
                var peers =
                    await GetNeighbors(neighbors[i], target, timeout, cancellationToken);
                history.Add(neighbors[i]);
                found.AddRange(peers.Where(peer => !found.Contains(peer)));
            }

            return found;
        }

        private async Task<IEnumerable<BoundPeer>> GetNeighbors(
            BoundPeer addressee,
            Address target,
            TimeSpan? timeout,
            CancellationToken cancellationToken)
        {
            var findPeer = new FindNeighbors(target);
            try
            {
                Message reply = await _transport.SendMessageWithReplyAsync(
                    addressee,
                    findPeer,
                    timeout,
                    cancellationToken
                );
                if (!(reply is Neighbors neighbors))
                {
                    throw new InvalidMessageException(
                        $"Reply to {nameof(FindNeighbors)} is invalid.",
                        reply
                    );
                }

                return neighbors.Found;
            }
            catch (InvalidTimestampException)
            {
                _logger.Debug($"Reply of {nameof(GetNeighbors)}'s timestamp is stale.");
                return ImmutableArray<BoundPeer>.Empty;
            }
            catch (TimeoutException)
            {
                RemovePeer(addressee);
                return ImmutableArray<BoundPeer>.Empty;
            }
        }

        // Send pong back to remote
        private async Task ReceivePingAsync(Ping ping)
        {
            if (ping.Remote.Address.Equals(_address))
            {
                throw new ArgumentException(
                    "Cannot receive ping from self");
            }

            var pong = new Pong
            {
                Identity = ping.Identity,
            };

            await _transport.ReplyMessageAsync(pong, default);
        }

        /// <summary>
        /// Process <see cref="Peer"/>s that is replied by sending <see cref="FindNeighbors"/>
        /// request.
        /// </summary>
        /// <param name="history"><see cref="Peer"/>s that already searched.</param>
        /// <param name="dialHistory"><see cref="Peer"/>s that ping sent.</param>
        /// <param name="found"><see cref="Peer"/>s that found.</param>
        /// <param name="target">The target <see cref="Address"/> to search.</param>
        /// <param name="depth">Target depth of recursive operation. If -1 is given,
        /// it runs until the closest peer is found.</param>
        /// <param name="timeout"><see cref="TimeSpan"/> for next depth's
        /// <see cref="FindPeerAsync"/> operation.</param>
        /// <param name="cancellationToken">A cancellation token used to propagate notification
        /// that this operation should be canceled.</param>
        /// <returns>An awaitable task without value.</returns>
        /// <exception cref="TimeoutException">Thrown when all peers that found are
        /// not online.</exception>
        private async Task ProcessFoundAsync(
            ConcurrentBag<BoundPeer> history,
            ConcurrentBag<BoundPeer> dialHistory,
            IEnumerable<BoundPeer> found,
            Address target,
            int depth,
            TimeSpan? timeout,
            CancellationToken cancellationToken)
        {
            List<BoundPeer> peers = found.Where(
                peer =>
                    !peer.Address.Equals(_address) &&
                    !_table.Contains(peer) &&
                    !history.Contains(peer)).ToList();

            if (peers.Count == 0)
            {
                _logger.Verbose("No any neighbor received.");
                return;
            }

            peers = Kademlia.SortByDistance(peers, target).ToList();

            IReadOnlyList<BoundPeer> closestCandidate =
                _table.Neighbors(target, _table.BucketSize, false);

            Task[] awaitables = peers
                .Where(peer => !dialHistory.Contains(peer))
                .Select(
                    peer =>
                    {
                        dialHistory.Add(peer);
                        return PingAsync(peer, _requestTimeout, cancellationToken);
                    }
                ).ToArray();
            try
            {
                await Task.WhenAll(awaitables);
            }
            catch (Exception)
            {
                IEnumerable<AggregateException> exceptions = awaitables
                    .Where(t => t.IsFaulted)
                    .Select(t => t.Exception);
                foreach (var ae in exceptions)
                {
                    var isTimeout = false;
                    foreach (var ie in ae.InnerExceptions)
                    {
                        if (ie is PingTimeoutException pte)
                        {
                            peers.Remove(pte.Target);
                            isTimeout = true;
                            break;
                        }
                    }

                    if (isTimeout)
                    {
                        break;
                    }

                    _logger.Warning(
                        ae,
                        "Some responses from neighbors found unexpectedly terminated: {ae}",
                        ae
                    );
                }
            }

            var findPeerTasks = new List<Task>();
            Peer closestKnown = closestCandidate.FirstOrDefault();
            var count = 0;
            foreach (var peer in peers)
            {
                if (!(closestKnown is null) &&
                   string.CompareOrdinal(
                       Kademlia.CalculateDistance(peer.Address, target).ToHex(),
                       Kademlia.CalculateDistance(closestKnown.Address, target).ToHex()
                   ) >= 1)
                {
                    break;
                }

                if (history.Contains(peer))
                {
                    continue;
                }

                findPeerTasks.Add(FindPeerAsync(
                    history,
                    dialHistory,
                    target,
                    peer,
                    depth == -1 ? depth : depth - 1,
                    timeout,
                    cancellationToken));
                if (count++ >= _findConcurrency)
                {
                    break;
                }
            }

            try
            {
                await Task.WhenAll(findPeerTasks);
            }
            catch (Exception e)
            {
                _logger.Error(
                    e,
                    "Some FindPeer tasks were unexpectedly terminated: {Exception}",
                    e
                );
            }
        }

        // FIXME: this method is not safe from amplification attack
        // maybe ping/pong/ping/pong is required
        private async Task ReceiveFindPeerAsync(FindNeighbors findNeighbors)
        {
            IEnumerable<BoundPeer> found =
                _table.Neighbors(findNeighbors.Target, _table.BucketSize, true);

            Neighbors neighbors = new Neighbors(found)
            {
                Identity = findNeighbors.Identity,
            };

            await _transport.ReplyMessageAsync(neighbors, default);
        }
    }
}
