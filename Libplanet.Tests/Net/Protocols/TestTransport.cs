using System;
using System.Collections.Concurrent;
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
using Nito.AsyncEx;
using Serilog;

namespace Libplanet.Tests.Net.Protocols
{
    internal class TestTransport : ITransport
    {
        private static readonly PrivateKey VersionSigner = new PrivateKey();
        private static readonly AppProtocolVersion AppProtocolVersion =
            AppProtocolVersion.Sign(VersionSigner, 1);

        private readonly Dictionary<Address, TestTransport> _transports;
        private readonly ILogger _logger;
        private readonly ConcurrentDictionary<byte[], Address> _peersToReply;
        private readonly ConcurrentDictionary<byte[], Message> _replyToReceive;
        private readonly AsyncCollection<Request> _requests;
        private readonly List<string> _ignoreTestMessageWithData;
        private readonly PrivateKey _privateKey;
        private readonly Random _random;
        private readonly bool _blockBroadcast;

        private TaskCompletionSource<object> _runningEvent;
        private CancellationTokenSource _swarmCancellationTokenSource;
        private TimeSpan _networkDelay;
        private bool _disposed;

        public TestTransport(
            Dictionary<Address, TestTransport> transports,
            PrivateKey privateKey,
            bool blockBroadcast,
            int tableSize,
            int bucketSize,
            TimeSpan? networkDelay)
        {
            _runningEvent = new TaskCompletionSource<object>();
            _privateKey = privateKey;
            _blockBroadcast = blockBroadcast;
            var loggerId = _privateKey.ToAddress().ToHex();
            _logger = Log.ForContext<TestTransport>()
                .ForContext("Address", loggerId);

            _peersToReply = new ConcurrentDictionary<byte[], Address>();
            _replyToReceive = new ConcurrentDictionary<byte[], Message>();
            ReceivedMessages = new ConcurrentBag<Message>();
            MessageReceived = new AsyncAutoResetEvent();
            _transports = transports;
            _transports[privateKey.ToAddress()] = this;
            _networkDelay = networkDelay ?? TimeSpan.Zero;
            _requests = new AsyncCollection<Request>();
            _ignoreTestMessageWithData = new List<string>();
            _random = new Random();
            Table = new RoutingTable(Address, tableSize, bucketSize);
            ProcessMessageHandler = new AsyncDelegate<Message>();
            Protocol = new KademliaProtocol(Table, this, Address);
            MessageHistory = new FixedSizedQueue<Message>(30);
        }

        public AsyncDelegate<Message> ProcessMessageHandler { get; }

        public AsyncAutoResetEvent MessageReceived { get; }

        public Address Address => _privateKey.ToAddress();

        public Peer AsPeer => new BoundPeer(
            _privateKey.PublicKey,
            new DnsEndPoint("localhost", 1234));

        public IReadOnlyList<BoundPeer> Peers => Table.Peers;

        public DateTimeOffset? LastMessageTimestamp { get; private set; }

        public bool Running
        {
            get => _runningEvent.Task.Status == TaskStatus.RanToCompletion;

            private set
            {
                if (value)
                {
                    _runningEvent.TrySetResult(null);
                }
                else
                {
                    _runningEvent = new TaskCompletionSource<object>();
                }
            }
        }

        public ConcurrentQueue<Message> MessageHistory { get; }

        internal ConcurrentBag<Message> ReceivedMessages { get; }

        internal RoutingTable Table { get; }

        internal IProtocol Protocol { get; }

        public void Dispose()
        {
            if (!_disposed)
            {
                _swarmCancellationTokenSource?.Cancel();
                Running = false;
                _disposed = true;
            }
        }

        public async Task StartAsync(
            CancellationToken cancellationToken = default(CancellationToken))
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            _logger.Debug("Starting transport of {Peer}.", AsPeer);
            _swarmCancellationTokenSource = new CancellationTokenSource();
            CancellationToken token = cancellationToken.Equals(CancellationToken.None)
                ? _swarmCancellationTokenSource.Token
                : CancellationTokenSource
                    .CreateLinkedTokenSource(
                        _swarmCancellationTokenSource.Token, cancellationToken)
                    .Token;
            Running = true;
            await ProcessRuntime(token);
        }

        public async Task StopAsync(
            TimeSpan waitFor,
            CancellationToken cancellationToken = default(CancellationToken))
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            if (Running)
            {
                _logger.Debug("Stopping transport of {Peer}.", AsPeer);
                _swarmCancellationTokenSource.Cancel();
                Running = false;
            }

            await Task.Delay(waitFor, cancellationToken);
        }

        /// <inheritdoc cref="ITransport.WaitForRunningAsync"/>
        public Task WaitForRunningAsync() => _runningEvent.Task;

        public async Task BootstrapAsync(
            IEnumerable<Peer> bootstrapPeers,
            TimeSpan? pingSeedTimeout = null,
            TimeSpan? findPeerTimeout = null,
            int depth = 3,
            CancellationToken cancellationToken = default(CancellationToken))
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            IEnumerable<BoundPeer> peers = bootstrapPeers.OfType<BoundPeer>();

            await BootstrapAsync(
                peers,
                pingSeedTimeout,
                findPeerTimeout,
                depth,
                cancellationToken);
        }

#pragma warning disable S4457 // Cannot split the method since method is in interface
        public async Task BootstrapAsync(
            IEnumerable<BoundPeer> bootstrapPeers,
            TimeSpan? pingSeedTimeout = null,
            TimeSpan? findPeerTimeout = null,
            int depth = 3,
            CancellationToken cancellationToken = default(CancellationToken))
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            if (!Running)
            {
                throw new TransportException("Start transport before use.");
            }

            if (bootstrapPeers is null)
            {
                throw new ArgumentNullException(nameof(bootstrapPeers));
            }

            await Protocol.BootstrapAsync(
                bootstrapPeers.ToImmutableList(),
                pingSeedTimeout,
                findPeerTimeout,
                Kademlia.MaxDepth,
                cancellationToken);
        }

        public Task SendMessageAsync(
            BoundPeer peer,
            Message message,
            CancellationToken cancellationToken)
            => SendMessageWithReplyAsync(
                peer,
                message,
                TimeSpan.FromSeconds(3),
                cancellationToken);

        public Task AddPeersAsync(
            IEnumerable<Peer> peers,
            TimeSpan? timeout,
            CancellationToken cancellationToken = default(CancellationToken))
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            if (!Running)
            {
                throw new TransportException("Start transport before use.");
            }

            if (peers is null)
            {
                throw new ArgumentNullException(nameof(peers));
            }

            async Task DoAddPeersAsync()
            {
                try
                {
                    KademliaProtocol kp = (KademliaProtocol)Protocol;

                    var tasks = new List<Task>();
                    foreach (var peer in peers)
                    {
                        if (peer is BoundPeer boundPeer)
                        {
                            tasks.Add(
                                kp.PingAsync(
                                    boundPeer,
                                    timeout: timeout,
                                    cancellationToken: cancellationToken));
                        }
                    }

                    _logger.Verbose("Trying to ping all {PeersNumber} peers.", tasks.Count);
                    await Task.WhenAll(tasks);
                    _logger.Verbose("Update complete.");
                }
                catch (DifferentAppProtocolVersionException)
                {
                    _logger.Debug("Different version encountered during AddPeersAsync().");
                }
                catch (PingTimeoutException)
                {
                    var msg =
                        $"Timeout occurred during {nameof(AddPeersAsync)}() after {timeout}.";
                    _logger.Debug(msg);
                    throw new TimeoutException(msg);
                }
                catch (TaskCanceledException)
                {
                    _logger.Debug($"Task is cancelled during {nameof(AddPeersAsync)}().");
                }
                catch (Exception e)
                {
                    _logger.Error(
                        e,
                        $"Unexpected exception occurred during {nameof(AddPeersAsync)}().");
                    throw;
                }
            }

            return DoAddPeersAsync();
        }

        public void SendPing(Peer target, TimeSpan? timeSpan = null)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            if (!Running)
            {
                throw new TransportException("Start transport before use.");
            }

            if (!(target is BoundPeer boundPeer))
            {
                throw new ArgumentException("Target peer does not have endpoint.", nameof(target));
            }

            Task.Run(() =>
            {
                _ = (Protocol as KademliaProtocol).PingAsync(
                    boundPeer,
                    timeSpan,
                    default(CancellationToken));
            });
        }

        public void BroadcastTestMessage(Address? except, string data)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            if (!Running)
            {
                throw new TransportException("Start transport before use.");
            }

            var message = new TestMessage(data) { Remote = AsPeer };
            _ignoreTestMessageWithData.Add(data);
            BroadcastMessage(except, message);
        }

        public void BroadcastMessage(Address? except, Message message)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            var peers = Table.PeersToBroadcast(except);
            var peersString = string.Join(", ", peers.Select(peer => peer.Address));
            _logger.Debug(
                "Broadcasting test message {Data} to {Count} peers which are: {Peers}",
                ((TestMessage)message).Data,
                peers.Count,
                peersString);
            foreach (var peer in peers)
            {
                _requests.Add(new Request()
                {
                    RequestTime = DateTimeOffset.UtcNow,
                    Message = message,
                    Target = peer,
                });
            }
        }

#pragma warning disable S4457 // Cannot split the method since method is in interface
        public async Task<Message> SendMessageWithReplyAsync(
            BoundPeer peer,
            Message message,
            TimeSpan? timeout,
            CancellationToken cancellationToken)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            if (!Running)
            {
                throw new TransportException("Start transport before use.");
            }

            if (!(peer is BoundPeer boundPeer))
            {
                throw new ArgumentException("Target peer is not a BoundPeer.");
            }

            message.Remote = AsPeer;
            var bytes = new byte[10];
            _random.NextBytes(bytes);
            message.Identity = _privateKey.ToAddress().ByteArray.Concat(bytes).ToArray();
            var sendTime = DateTimeOffset.UtcNow;
            _logger.Debug("Adding request of {Message} of {Identity}.", message, message.Identity);
            await _requests.AddAsync(
                new Request()
                {
                    RequestTime = sendTime,
                    Message = message,
                    Target = peer,
                }, cancellationToken);

            while (!cancellationToken.IsCancellationRequested &&
                   !_replyToReceive.ContainsKey(message.Identity))
            {
                if (DateTimeOffset.UtcNow - sendTime > (timeout ?? TimeSpan.MaxValue))
                {
                    _logger.Error(
                        "Reply of {Message} of {identity} did not received in " +
                        "expected timespan {TimeSpan}.",
                        message,
                        message.Identity,
                        timeout ?? TimeSpan.MaxValue);
                    throw new TimeoutException(
                        $"Timeout occurred during {nameof(SendMessageWithReplyAsync)}().");
                }

                await Task.Delay(10, cancellationToken);
            }

            if (cancellationToken.IsCancellationRequested)
            {
                throw new OperationCanceledException(
                    $"Operation is canceled during {nameof(SendMessageWithReplyAsync)}().");
            }

            if (_replyToReceive.TryRemove(message.Identity, out Message reply))
            {
                _logger.Debug(
                    "Received reply {Reply} of message with identity {identity}.",
                    reply,
                    message.Identity);
                LastMessageTimestamp = DateTimeOffset.UtcNow;
                ReceivedMessages.Add(reply);
                MessageHistory.Enqueue(reply);
                MessageReceived.Set();
                return reply;
            }
            else
            {
                _logger.Error(
                    "Unexpected error occurred during " +
                    $"{nameof(SendMessageWithReplyAsync)}()");
                throw new SwarmException();
            }
        }
#pragma warning restore S4457 // Cannot split the method since method is in interface

        public async Task<IEnumerable<Message>> SendMessageWithReplyAsync(
            BoundPeer peer,
            Message message,
            TimeSpan? timeout,
            int expectedResponses,
            CancellationToken cancellationToken = default(CancellationToken))
        {
            return new[]
            {
                await SendMessageWithReplyAsync(peer, message, timeout, cancellationToken),
            };
        }

        public async Task ReplyMessageAsync(Message message, CancellationToken cancellationToken)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            if (!Running)
            {
                throw new TransportException("Start transport before use.");
            }

            _logger.Debug("Replying {Message}...", message);
            message.Remote = AsPeer;
            await Task.Delay(_networkDelay, cancellationToken);
            _transports[_peersToReply[message.Identity]].ReceiveReply(message);
            _peersToReply.TryRemove(message.Identity, out Address addr);
        }

        public async Task WaitForTestMessageWithData(
            string data,
            CancellationToken token = default(CancellationToken))
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            if (!Running)
            {
                throw new TransportException("Start transport before use.");
            }

            while (!token.IsCancellationRequested && !ReceivedTestMessageOfData(data))
            {
                await Task.Delay(10, token);
            }
        }

        public bool ReceivedTestMessageOfData(string data)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TestTransport));
            }

            return ReceivedMessages.OfType<TestMessage>().Any(msg => msg.Data == data);
        }

        private void ReceiveMessage(Message message)
        {
            if (_swarmCancellationTokenSource.IsCancellationRequested)
            {
                return;
            }

            if (!(message.Remote is BoundPeer boundPeer))
            {
                throw new ArgumentException("Sender of message is not a BoundPeer.");
            }

            MessageHistory.Enqueue(message);
            if (message is TestMessage testMessage)
            {
                if (_ignoreTestMessageWithData.Contains(testMessage.Data))
                {
                    _logger.Debug("Ignore received test message {Data}.", testMessage.Data);
                }
                else
                {
                    _logger.Debug("Received test message with {Data}.", testMessage.Data);
                    _ignoreTestMessageWithData.Add(testMessage.Data);
                    // If this transport is blocked for testing, do not broadcast.
                    if (!_blockBroadcast)
                    {
                        BroadcastTestMessage(testMessage.Remote.Address, testMessage.Data);
                    }
                }
            }
            else
            {
                _peersToReply[message.Identity] = boundPeer.Address;
            }

            LastMessageTimestamp = DateTimeOffset.UtcNow;
            ReceivedMessages.Add(message);
            _ = ProcessMessageHandler.InvokeAsync(message);
            MessageReceived.Set();
        }

        private void ReceiveReply(Message message)
        {
            _replyToReceive[message.Identity] = message;
        }

        private async Task ProcessRuntime(CancellationToken cancellationToken)
        {
            while (!cancellationToken.IsCancellationRequested)
            {
                Request req = await _requests.TakeAsync(cancellationToken);

                if (req.RequestTime + _networkDelay <= DateTimeOffset.UtcNow)
                {
                    _logger.Debug(
                        "Send {Message} with {Identity} to {Peer}.",
                        req.Message,
                        req.Message.Identity,
                        req.Target);
                    _transports[req.Target.Address].ReceiveMessage(req.Message);
                }
                else
                {
                    await _requests.AddAsync(req, cancellationToken);
                    await Task.Delay(10, cancellationToken);
                }
            }
        }

        private struct Request
        {
            public DateTimeOffset RequestTime;

            public BoundPeer Target;

            public Message Message;
        }
    }
}
