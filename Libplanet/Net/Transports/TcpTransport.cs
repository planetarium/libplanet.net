#nullable enable
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Threading;
using System.Threading.Tasks;
using Libplanet.Crypto;
using Libplanet.Net.Messages;
using Libplanet.Net.Protocols;
using Libplanet.Stun;
using Nito.AsyncEx;
using Serilog;

namespace Libplanet.Net.Transports
{
    public class TcpTransport : ITransport
    {
        public static readonly byte[] MagicCookie = { 0x4c, 0x50 }; // 'L', 'P'

        private const int MessageHistoryCapacity = 30;
        private const int ListenerBacklog = 100;
        private const int MaxReplyStreams = 3000;

        // TODO: Should be configurable (ex. SwarmOptions.MaxTimeout)
        private static readonly TimeSpan ListenerLifetime = TimeSpan.FromMinutes(2);

        // TURN Permission lifetime was defined in RFC 5766
        // see also https://tools.ietf.org/html/rfc5766#section-8
        private static readonly TimeSpan TurnPermissionLifetime =
            TimeSpan.FromMinutes(5);

        private readonly RoutingTable _table;
        private readonly PrivateKey _privateKey;
        private readonly AppProtocolVersion _appProtocolVersion;
        private readonly IImmutableSet<PublicKey>? _trustedAppProtocolVersionSigners;
        private readonly string? _host;
        private readonly DifferentAppProtocolVersionEncountered?
            _differentAppProtocolVersionEncountered;

        private readonly IList<IceServer>? _iceServers;
        private readonly ILogger _logger;
        private readonly TimeSpan? _messageLifespan;

        private readonly CancellationTokenSource _turnCancellationTokenSource;

        private readonly ConcurrentDictionary<Guid, ReplyStream> _streams;

        private TaskCompletionSource<object> _runningEvent;
        private CancellationTokenSource _runtimeCancellationTokenSource;
        private CancellationToken _cancellationToken;

        private int _listenPort;
        private DnsEndPoint? _hostEndPoint;
        private TcpListener? _listener;
        private TurnClient? _turnClient;

        private bool _disposed;

        public TcpTransport(
            RoutingTable table,
            PrivateKey privateKey,
            AppProtocolVersion appProtocolVersion,
            IImmutableSet<PublicKey>? trustedAppProtocolVersionSigners,
            string? host,
            int? listenPort,
            IEnumerable<IceServer> iceServers,
            DifferentAppProtocolVersionEncountered? differentAppProtocolVersionEncountered,
            TimeSpan? messageLifespan = null)
        {
            _runningEvent = null!;
            Running = false;

            _table = table;
            _privateKey = privateKey;
            _appProtocolVersion = appProtocolVersion;
            _trustedAppProtocolVersionSigners = trustedAppProtocolVersionSigners;
            _host = host;
            _listenPort = listenPort ?? 0;
            _differentAppProtocolVersionEncountered = differentAppProtocolVersionEncountered;
            _iceServers = iceServers?.ToList();
            _messageLifespan = messageLifespan;
            _streams = new ConcurrentDictionary<Guid, ReplyStream>();

            if (!(_host is null) && listenPort is { } listenPortAsInt)
            {
                _hostEndPoint = new DnsEndPoint(_host, listenPortAsInt);
            }

            if (_host == null && (_iceServers == null || !_iceServers.Any()))
            {
                throw new ArgumentException(
                    $"Swarm requires either {nameof(host)} or " +
                    $"{nameof(iceServers)}."
                );
            }

            _logger = Log.ForContext<TcpTransport>();
            _runtimeCancellationTokenSource = new CancellationTokenSource();
            _turnCancellationTokenSource = new CancellationTokenSource();
            ProcessMessageHandler = new AsyncDelegate<Message>();
            MessageHistory = new FixedSizedQueue<Message>(MessageHistoryCapacity);
        }

        /// <inheritdoc cref="ITransport.ProcessMessageHandler"/>
        public AsyncDelegate<Message> ProcessMessageHandler { get; }

        /// <inheritdoc cref="ITransport.AsPeer"/>
        public Peer AsPeer => EndPoint is null
            ? new Peer(_privateKey.PublicKey, PublicIPAddress)
            : new BoundPeer(_privateKey.PublicKey, EndPoint, PublicIPAddress);

        /// <inheritdoc cref="ITransport.Running"/>
        public DateTimeOffset? LastMessageTimestamp { get; private set; }

        public bool Running
        {
            get => _runningEvent?.Task.Status == TaskStatus.RanToCompletion;

            private set
            {
                if (value)
                {
                    _runningEvent?.TrySetResult(null!);
                }
                else
                {
                    _runningEvent = new TaskCompletionSource<object>();
                }
            }
        }

        public ConcurrentQueue<Message> MessageHistory { get; }

        internal IPAddress? PublicIPAddress => _turnClient?.PublicAddress;

        internal DnsEndPoint? EndPoint => _turnClient?.EndPoint ?? _hostEndPoint;

        public void Dispose()
        {
            if (!_disposed)
            {
                _listener?.Stop();
                _runtimeCancellationTokenSource.Cancel();
                _turnCancellationTokenSource.Cancel();

                _runtimeCancellationTokenSource.Dispose();
                _turnCancellationTokenSource.Dispose();
                StopAllStreams();
                Running = false;
                _disposed = true;
            }
        }

        public async Task StartAsync(CancellationToken cancellationToken = default)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TcpTransport));
            }

            if (Running)
            {
                throw new TransportException("Transport is already running.");
            }

            _listener = new TcpListener(new IPEndPoint(IPAddress.Any, _listenPort));
            _listener.Start(ListenerBacklog);

            // _listenPort might be 0, which is any, so it should be re-set.
            _listenPort = ((IPEndPoint)_listener.LocalEndpoint).Port;

            _logger.Information("Listen on {Port}", _listenPort);

            if (_host is null && !(_iceServers is null))
            {
                _turnClient = await IceServer.CreateTurnClient(_iceServers);
                await _turnClient.StartAsync(_listenPort, cancellationToken);

                _ = RefreshPermissions(cancellationToken);
            }

            _runtimeCancellationTokenSource =
                CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
            _cancellationToken = _runtimeCancellationTokenSource.Token;

            if (_turnClient is null || !_turnClient.BehindNAT)
            {
                string? host = _host ?? PublicIPAddress?.ToString();
                if (host is null)
                {
                    throw new TransportException("Host is null.");
                }

                _hostEndPoint = new DnsEndPoint(host, _listenPort);
            }

            List<Task> tasks = new List<Task>();

            tasks.Add(ReceiveMessageAsync(_cancellationToken));
            tasks.Add(ProcessRuntime(_cancellationToken));

            Running = true;
            _logger.Debug("Start to run. TurnClient: {Client}", _turnClient);

            await await Task.WhenAny(tasks);
        }

        public async Task StopAsync(TimeSpan waitFor, CancellationToken cancellationToken = default)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TcpTransport));
            }

            if (Running)
            {
                await Task.Delay(waitFor, cancellationToken);
                _listener?.Stop();
                _runtimeCancellationTokenSource.Cancel();
                _turnCancellationTokenSource.Cancel();
                StopAllStreams();
                Running = false;
            }
        }

        /// <inheritdoc cref="ITransport.WaitForRunningAsync"/>
        public Task WaitForRunningAsync() => _runningEvent.Task;

        public Task SendMessageAsync(
            BoundPeer peer,
            Message message,
            CancellationToken cancellationToken)
            => SendMessageWithReplyAsync(
                peer,
                message,
                TimeSpan.FromSeconds(3),
                0,
                cancellationToken);

        public async Task<Message> SendMessageWithReplyAsync(
            BoundPeer peer,
            Message message,
            TimeSpan? timeout,
            CancellationToken cancellationToken)
        {
            IEnumerable<Message> replies =
                await SendMessageWithReplyAsync(peer, message, timeout, 1, cancellationToken);
            Message reply = replies.First();

            return reply;
        }

        public async Task<IEnumerable<Message>> SendMessageWithReplyAsync(
            BoundPeer peer,
            Message message,
            TimeSpan? timeout,
            int expectedResponses,
            CancellationToken cancellationToken = default)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TcpTransport));
            }

            if (!(_turnClient is null) && _turnClient.BehindNAT)
            {
                await CreatePermission(peer);
            }

            if (expectedResponses < 0)
            {
                throw new ArgumentOutOfRangeException(nameof(expectedResponses));
            }

            Guid reqId;
            if (message.Identity is null)
            {
                reqId = Guid.NewGuid();
                message.Identity = reqId.ToByteArray();
            }
            else
            {
                reqId = new Guid(message.Identity);
            }

            _logger.Verbose(
                "Start to request {RequestId} to {Peer}: {Message}. (expected responses: {Count})",
                reqId,
                peer,
                message,
                expectedResponses
            );

            using var client = new TcpClient { LingerState = new LingerOption(true, 1) };
            try
            {
                await client.ConnectAsync(peer.EndPoint.Host, peer.EndPoint.Port);
                client.ReceiveTimeout = timeout?.Milliseconds ?? 0;
                await WriteMessageAsync(message, client, cancellationToken);
                _logger.Verbose(
                    "Successfully sent request {RequestId} to {Peer}: {Message}.",
                    reqId,
                    peer,
                    message
                );

                var replies = new List<Message>();
                using var timeoutCts = new CancellationTokenSource();
                if (expectedResponses != 0 && !(timeout is null))
                {
                    timeoutCts.CancelAfter(
                        (int)timeout.Value.TotalMilliseconds * expectedResponses);
                }

                using CancellationTokenSource linkedTcs =
                    CancellationTokenSource.CreateLinkedTokenSource(
                        timeoutCts.Token,
                        cancellationToken);
                while (expectedResponses > 0)
                {
                    try
                    {
                        // TODO: Should consider case where stream bytes exceeds buffer size.
                        Message received = await ReadMessageAsync(
                            client,
                            linkedTcs.Token);
                        _logger.Verbose(
                            "Received message was {Message}. Total: {Count}",
                            received,
                            replies.Count);
                        MessageHistory.Enqueue(received);
                        replies.Add(received);
                        expectedResponses--;
                    }
                    catch (TaskCanceledException)
                    {
                        if (timeoutCts.IsCancellationRequested)
                        {
                            var msg =
                                $"{nameof(SendMessageWithReplyAsync)}() timed out after " +
                                "{Timeout} of waiting a reply to {MessageType} ({RequestId}) " +
                                "from {PeerAddress}.";
                            _logger.Debug(
                                msg,
                                timeout,
                                message.GetType().Name,
                                reqId,
                                peer.Address);
                            throw new TimeoutException();
                        }

                        throw;
                    }
                }

                if (replies.Any())
                {
                    const string logMsg =
                        "Received {ReplyMessageCount} reply messages to {RequestId} " +
                        "from the {Peer}: {ReplyMessages}.";
                    _logger.Debug(logMsg, replies.Count, reqId, peer, replies);
                }

                return replies;
            }
            catch (DifferentAppProtocolVersionException e)
            {
                const string logMsg =
                    "{PeerAddress} sent a reply to {RequestId} with " +
                    "a different app protocol version; " +
                    "expected: {ExpectedVersion}; actual: {ActualVersion}.";
                _logger.Error(e, logMsg, peer.Address, reqId, e.ExpectedVersion, e.ActualVersion);
                throw;
            }
            catch (ArgumentException e)
            {
                // This exception is thrown on .NET framework when the given peer is invalid.
                _logger.Error(
                    e,
                    "ArgumentException occurred during {FName} to {RequestId}. {E}",
                    nameof(SendMessageWithReplyAsync),
                    reqId,
                    e);

                // To match with previous implementation, throws TimeoutException when it failed to
                // find peer to send message.
                throw new TimeoutException($"Cannot find peer {peer}.", e);
            }
            catch (SocketException e)
            {
                // This exception is thrown on .NET core when the given peer is invalid.
                _logger.Error(
                    e,
                    "SocketException occurred during {FName} to {RequestId}. {E}",
                    nameof(SendMessageWithReplyAsync),
                    reqId,
                    e);

                // To match with previous implementation, throws TimeoutException when it failed to
                // find peer to send message.
                throw new TimeoutException($"Cannot find peer {peer}.", e);
            }
            catch (InvalidMagicCookieException e)
            {
                _logger.Verbose(
                    "Magic cookie mismatch, ignored. (Expected: {Expected}, Actual: {Actual})",
                    e.Expected,
                    e.Actual);
                throw;
            }
        }

        public void BroadcastMessage(Address? except, Message message)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TcpTransport));
            }

            foreach (var peer in _table.PeersToBroadcast(except))
            {
                _ = SendMessageAsync(peer, message, _cancellationToken);
            }
        }

        public async Task ReplyMessageAsync(Message message, CancellationToken cancellationToken)
        {
            if (_disposed)
            {
                throw new ObjectDisposedException(nameof(TcpTransport));
            }

            var id = new Guid(message.Identity);
            _logger.Verbose("Trying to reply message. ID: {Id}", id);
            if (_streams.TryGetValue(id, out ReplyStream stream))
            {
                _logger.Verbose("Send reply message {Message}", message);
                try
                {
                    _logger.Verbose("Start to writing reply {Message}.", message);
                    using var @lock = stream.Lock.Lock();
                    await WriteMessageAsync(message, stream.Client, _cancellationToken);
                }
                catch (IOException)
                {
                    _logger.Verbose("Connection is lost");
                    _ = TryRemoveStreamAsync(id, _cancellationToken);
                }
            }
        }

        internal async Task WriteMessageAsync(
            Message message,
            TcpClient client,
            CancellationToken cancellationToken)
        {
            byte[] serialized = message.Serialize(
                _privateKey,
                AsPeer,
                DateTimeOffset.UtcNow,
                _appProtocolVersion);
            int length = serialized.Length;
            var buffer = new byte[MagicCookie.Length + sizeof(int) + length];
            MagicCookie.CopyTo(buffer, 0);
            BitConverter.GetBytes(length).CopyTo(buffer, MagicCookie.Length);
            serialized.CopyTo(buffer, MagicCookie.Length + sizeof(int));
            NetworkStream stream = client.GetStream();

            // NOTE: Stream is forced to be closed because NetStream.WriteAsync()'s
            // cancellation token never works in .NET Framework.
            using (cancellationToken.Register(() => stream.Close()))
            {
                try
                {
                    await stream.WriteAsync(buffer, 0, buffer.Length, default);
                }
                catch (Exception)
                {
                    if (cancellationToken.IsCancellationRequested)
                    {
                        throw new TaskCanceledException();
                    }

                    throw;
                }
            }
        }

        internal async Task<Message> ReadMessageAsync(
            TcpClient client,
            CancellationToken cancellationToken)
        {
            var content = new List<byte>();
            byte[] buffer = new byte[1000];
            NetworkStream stream = client.GetStream();

            // NOTE: Stream is forced to be closed because NetStream.ReadAsync()'s
            // cancellation token never works in .NET Framework.
            using (cancellationToken.Register(() => stream.Close()))
            {
                try
                {
                    // May read shorter than MagicCookie's length just by network condition
                    int bytesRead = await stream.ReadAsync(buffer, 0, MagicCookie.Length, default);
                    if (bytesRead < MagicCookie.Length ||
                        !buffer.Take(MagicCookie.Length).SequenceEqual(MagicCookie))
                    {
                        throw new InvalidMagicCookieException(MagicCookie, buffer.Take(bytesRead));
                    }

                    await stream.ReadAsync(buffer, 0, sizeof(int), default);
                    int bytesLeft = BitConverter.ToInt32(buffer.Take(sizeof(int)).ToArray(), 0);

                    while (bytesLeft != 0)
                    {
                        bytesRead = await stream.ReadAsync(
                            buffer,
                            0,
                            bytesLeft < 1000 ? bytesLeft : 1000,
                            default);
                        content.AddRange(buffer.Take(bytesRead));
                        bytesLeft -= bytesRead;
                    }
                }
                catch (InvalidMagicCookieException)
                {
                    if (cancellationToken.IsCancellationRequested)
                    {
                        throw new TaskCanceledException();
                    }

                    throw;
                }
                catch (Exception)
                {
                    if (cancellationToken.IsCancellationRequested)
                    {
                        throw new TaskCanceledException();
                    }

                    _logger.Error(
                        e,
                        "Error occurred during {FName}() {E}",
                        nameof(ReadMessageAsync),
                        e);
                    throw;
                }
            }

            _logger.Verbose("Received {Bytes} bytes from network stream.", content.Count);

            Message message = Message.Deserialize(
                content.ToArray(),
                _appProtocolVersion,
                _trustedAppProtocolVersionSigners,
                _differentAppProtocolVersionEncountered,
                _messageLifespan);

            _logger.Verbose(
                "ReadMessageAsync success. Received message {Message} from network stream.",
                message);
            return message;
        }

        private async Task ReceiveMessageAsync(CancellationToken cancellationToken)
        {
            while (!(cancellationToken.IsCancellationRequested || _listener is null))
            {
                try
                {
                    TcpClient client = await _listener.AcceptTcpClientAsync();
                    client.LingerState = new LingerOption(true, 1);
                    _logger.Verbose("Connected to tcp client.");
                    Guid guid = Guid.NewGuid();
                    _logger.Verbose("Start to accept message of {Id}.", guid);

                    // TODO: Maximum message processor should be limited.
                    _ = AcceptAsync(client, cancellationToken)
                        .ContinueWith<Task>(
                            async t =>
                            {
                                _logger.Verbose("Ended to accept message of {Id}.", guid);
                                try
                                {
                                    // Wait 15 seconds to close client to receive ACK from TURN.
                                    await Task.Delay(
                                        15 * 1000,
                                        _runtimeCancellationTokenSource.Token);
                                }
                                finally
                                {
                                    client.Close();
                                    await TryRemoveStreamAsync(guid, cancellationToken);
                                }
                            },
                            cancellationToken);
                }
                catch (ObjectDisposedException)
                {
                    _logger.Warning("TCPListener is disposed.");
                    break;
                }
            }
        }

        private async Task AcceptAsync(
            TcpClient client,
            CancellationToken cancellationToken)
        {
            try
            {
                _logger.Verbose("Trying to receive message");
                Message message = await ReadMessageAsync(client, cancellationToken);
                MessageHistory.Enqueue(message);
                LastMessageTimestamp = DateTimeOffset.UtcNow;
                _logger.Debug(
                    "A message has parsed: {Message}, from {Remove}",
                    message,
                    message.Remote);

                var id = new Guid(message.Identity);
                await TryAddStreamAsync(id, client, cancellationToken);
                await ProcessMessageHandler.InvokeAsync(message);
            }
            catch (DifferentAppProtocolVersionException dapve)
            {
                _logger.Debug("Message from peer with different version received.");
                var differentVersion = new DifferentVersion
                {
                    Identity = dapve.Identity,
                };

                await WriteMessageAsync(differentVersion, client, cancellationToken);
            }
            catch (IOException)
            {
                _logger.Verbose("Connection is lost.");
            }
            catch (InvalidMagicCookieException e)
            {
                _logger.Verbose(
                    "Magic cookie mismatch, ignored. (Expected: {Expected}, Actual: {Actual})",
                    e.Expected,
                    e.Actual);
            }
            catch (Exception e)
            {
                _logger.Error(
                    e,
                    "Unexpected exception occurred during {FName}(). {E}",
                    nameof(AcceptAsync),
                    e);
                throw;
            }
        }

        private async Task RefreshPermissions(
            CancellationToken cancellationToken)
        {
            TimeSpan lifetime = TurnPermissionLifetime;
            while (!cancellationToken.IsCancellationRequested)
            {
                try
                {
                    await Task.Delay(lifetime - TimeSpan.FromMinutes(1), cancellationToken);
                    _logger.Debug("Refreshing permissions...");
                    await Task.WhenAll(_table.Peers.Select(CreatePermission));
                    cancellationToken.ThrowIfCancellationRequested();
                }
                catch (OperationCanceledException e)
                {
                    _logger.Warning(e, "{FName}() is cancelled.", nameof(RefreshPermissions));
                    throw;
                }
                catch (Exception e)
                {
                    _logger.Error(
                        e,
                        "An unexpected exception occurred during {FName}(): {E}",
                        nameof(RefreshPermissions),
                        e);
                }
            }
        }

        private async Task CreatePermission(BoundPeer peer)
        {
            if (_turnClient is null)
            {
                throw new TransportException(
                    "CreatePermission should not be called when the turn client does not exists");
            }

            using var cts = new CancellationTokenSource();
            IPAddress[] ips;

            // Cancellation After 2.5 sec
            cts.CancelAfter(2500);
            if (peer.PublicIPAddress is null)
            {
                string peerHost = peer.EndPoint.Host;
                if (IPAddress.TryParse(peerHost, out IPAddress asIp))
                {
                    ips = new[] { asIp };
                }
                else
                {
                    ips = await Dns.GetHostAddressesAsync(peerHost);
                }
            }
            else
            {
                ips = new[] { peer.PublicIPAddress };
            }

            try
            {
                foreach (IPAddress ip in ips)
                {
                    var ep = new IPEndPoint(ip, peer.EndPoint.Port);
                    if (IPAddress.IsLoopback(ip))
                    {
                        // This translation is only used in test case because a
                        // seed node exposes loopback address as public address to
                        // other node in test case
                        ep = await _turnClient.GetMappedAddressAsync(cts.Token);
                    }

                    // FIXME Can we really ignore IPv6 case?
                    if (ip.AddressFamily.Equals(AddressFamily.InterNetwork))
                    {
                        await _turnClient.CreatePermissionAsync(ep, cts.Token);
                    }
                }
            }
            catch (TaskCanceledException tce)
            {
                if (cts.IsCancellationRequested)
                {
                    _logger.Debug(
                        tce,
                        "Timeout occurred during {FName}",
                        nameof(CreatePermission));
                }
                else
                {
                    throw;
                }
            }
        }

        private async Task ProcessRuntime(CancellationToken cancellationToken)
        {
            while (!cancellationToken.IsCancellationRequested)
            {
                foreach (KeyValuePair<Guid, ReplyStream> pair in _streams)
                {
                    // FIXME: This lifetime related disposing logic can be tested?
                    if (pair.Value.SpawnAt + ListenerLifetime < DateTimeOffset.UtcNow)
                    {
                        _ = TryRemoveStreamAsync(pair.Key, cancellationToken);
                    }
                }

                await Task.Delay(100, cancellationToken);
            }
        }

        private async Task TryAddStreamAsync(
            Guid id,
            TcpClient client,
            CancellationToken cancellationToken)
        {
            while (_streams.Count > MaxReplyStreams && !cancellationToken.IsCancellationRequested)
            {
                await Task.Delay(100, cancellationToken);
            }

            _streams.TryAdd(id, new ReplyStream(client, DateTimeOffset.UtcNow));
            _logger.Verbose("Added stream to the collection. {Id}", id);
        }

        private async Task TryRemoveStreamAsync(Guid id, CancellationToken cancellationToken)
        {
            if (!_streams.TryRemove(id, out ReplyStream stream))
            {
                return;
            }

            using var @lock = await stream.Lock.LockAsync(cancellationToken);
            try
            {
                stream.Client.Close();
                stream.Client.Dispose();
            }
            catch (ObjectDisposedException)
            {
            }

            _logger.Verbose("Removed stream from the collection. {Id}", id);
        }

        private void StopAllStreams()
        {
            List<Task> tasks = new List<Task>();
            foreach (var id in _streams.Keys)
            {
                tasks.Add(TryRemoveStreamAsync(id, default));
            }

            Task.WhenAll(tasks).Wait();
        }

        private struct ReplyStream
        {
            public ReplyStream(TcpClient client, DateTimeOffset spawnAt)
            {
                Client = client;
                SpawnAt = spawnAt;
                Lock = new AsyncLock();
            }

            public DateTimeOffset SpawnAt { get; }

            public TcpClient Client { get; }

            public AsyncLock Lock { get; }
        }
    }
}
