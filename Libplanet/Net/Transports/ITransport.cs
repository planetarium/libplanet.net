using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Threading;
using System.Threading.Tasks;
using Libplanet.Net.Messages;

namespace Libplanet.Net.Transports
{
    /// <summary>
    /// An interface to handle peer-to-peer networking, including <see cref="Message"/> exchanging
    /// and <see cref="Peer"/> managing.
    /// </summary>
    public interface ITransport : IDisposable
    {
        /// <summary>
        /// The list of tasks invoked when a message that is not
        /// a reply is received. To handle reply, please use <see cref=
        /// "SendMessageWithReplyAsync(BoundPeer,Message,TimeSpan?,CancellationToken)"/>.
        /// </summary>
        AsyncDelegate<Message> ProcessMessageHandler { get; }

        /// <summary>
        /// <see cref="Peer"/> representation of <see cref="ITransport"/>.
        /// </summary>
        [Pure]
        Peer AsPeer { get; }

        /// <summary>
        /// The <see cref="DateTimeOffset"/> of the last message was received.
        /// </summary>
        [Pure]
        DateTimeOffset? LastMessageTimestamp { get; }

        /// <summary>
        /// Whether this <see cref="ITransport"/> instance is running.
        /// </summary>
        /// <value>Gets the value indicates whether the instance is running.</value>
        [Pure]
        bool Running { get; }

        /// <summary>
        /// A fixed sized queue that keeps history of <see cref="Message"/> received.
        /// It saves at most 30 recent <see cref="Message"/>s.
        /// </summary>
        [Pure]
        ConcurrentQueue<Message> MessageHistory { get; }

        /// <summary>
        /// Initiates and runs transport layer.
        /// </summary>
        /// <param name="cancellationToken">
        /// A cancellation token used to propagate notification that this
        /// operation should be canceled.</param>
        /// <returns>An awaitable task without value.</returns>
        /// <exception cref="ObjectDisposedException">
        /// Thrown when <see cref="ITransport"/> instance is already disposed.</exception>
        Task StartAsync(CancellationToken cancellationToken = default);

        /// <summary>
        /// Stops running transport layer.
        /// </summary>
        /// <param name="waitFor">The <see cref="TimeSpan"/> of delay
        /// before actual stopping.</param>
        /// <param name="cancellationToken">
        /// A cancellation token used to propagate notification that this
        /// operation should be canceled.</param>
        /// <returns>An awaitable task without value.</returns>
        /// <exception cref="ObjectDisposedException">
        /// Thrown when <see cref="ITransport"/> instance is already disposed.</exception>
        Task StopAsync(
            TimeSpan waitFor,
            CancellationToken cancellationToken = default);

        /// <summary>
        /// Waits until this <see cref="ITransport"/> instance gets started to run.
        /// </summary>
        /// <returns>A <see cref="Task"/> completed when <see cref="ITransport.Running"/>
        /// property becomes <c>true</c>.</returns>
        Task WaitForRunningAsync();

        /// <summary>
        /// Sends the <paramref name="message"/> to given <paramref name="peer"/>.
        /// </summary>
        /// <param name="peer">A <see cref="Peer"/> to send message to.</param>
        /// <param name="message">A <see cref="Message"/> to send.</param>
        /// <param name="cancellationToken">
        /// A cancellation token used to propagate notification that this
        /// operation should be canceled.</param>
        /// <returns>An awaitable task without value.</returns>
        /// <exception cref="ObjectDisposedException">
        /// Thrown when <see cref="ITransport"/> instance is already disposed.</exception>
        Task SendMessageAsync(BoundPeer peer, Message message, CancellationToken cancellationToken);

        /// <summary>
        /// Sends the <paramref name="message"/>
        /// to given <paramref name="peer"/> and waits for its single reply.
        /// </summary>
        /// <param name="peer">A <see cref="Peer"/> to send message to.</param>
        /// <param name="message">A <see cref="Message"/> to send.</param>
        /// <param name="timeout">A timeout of waiting for the reply of the message.</param>
        /// <param name="cancellationToken">
        /// A cancellation token used to propagate notification that this
        /// operation should be canceled.</param>
        /// <returns>The replies of the <paramref name="message"/>
        /// sent by <paramref name="peer"/>.</returns>
        /// <exception cref="ObjectDisposedException">
        /// Thrown when <see cref="ITransport"/> instance is already disposed.</exception>
        Task<Message> SendMessageWithReplyAsync(
            BoundPeer peer,
            Message message,
            TimeSpan? timeout,
            CancellationToken cancellationToken);

        /// <summary>
        /// Sends the <paramref name="message"/>
        /// to given <paramref name="peer"/> and waits for its multiple replies.
        /// </summary>
        /// <param name="peer">A <see cref="Peer"/> to send message to.</param>
        /// <param name="message">A <see cref="Message"/> to send.</param>
        /// <param name="timeout">A timeout of waiting for the reply of the message.</param>
        /// <param name="expectedResponses">The number of expected replies for the message.</param>
        /// <param name="cancellationToken">
        /// A cancellation token used to propagate notification that this
        /// operation should be canceled.</param>
        /// <returns>The replies of the <paramref name="message"/>
        /// sent by <paramref name="peer"/>.</returns>
        /// <exception cref="ObjectDisposedException">
        /// Thrown when <see cref="ITransport"/> instance is already disposed.</exception>
        Task<IEnumerable<Message>> SendMessageWithReplyAsync(
            BoundPeer peer,
            Message message,
            TimeSpan? timeout,
            int expectedResponses,
            CancellationToken cancellationToken = default);

        /// <summary>
        /// Broadcasts the <paramref name="message"/> to peers selected from the routing table.
        /// </summary>
        /// <param name="except">An <see cref="Address"/> to exclude from broadcasting.
        /// If <c>null</c> is given, no peers will be excluded.</param>
        /// <param name="message">A <see cref="Message"/> to broadcast.</param>
        /// <exception cref="ObjectDisposedException">
        /// Thrown when <see cref="ITransport"/> instance is already disposed.</exception>
        void BroadcastMessage(Address? except, Message message);

        /// <summary>
        /// Replies message.
        /// </summary>
        /// <remarks>
        /// The <see cref="Message.Identity"/> of the given <paramref name="message"/> must be
        /// matched to <see cref="Message.Identity"/> of a message corresponding to the given
        /// <paramref name="message"/>.
        /// </remarks>
        /// <param name="message">A <see cref="Message"/> to reply.</param>
        /// <param name="cancellationToken">
        /// A cancellation token used to propagate notification that this
        /// operation should be canceled.</param>
        /// <returns>An awaitable task without value.</returns>
        /// <exception cref="ObjectDisposedException">
        /// Thrown when <see cref="ITransport"/> instance is already disposed.</exception>
        Task ReplyMessageAsync(Message message, CancellationToken cancellationToken);
    }
}
