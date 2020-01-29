using System.Collections.Concurrent;

namespace Libplanet
{
    /// <summary>
    /// Implements a <see cref="ConcurrentQueue{T}"/> of a fixed size.
    /// </summary>
    /// <typeparam name="T">Specifies the type of elements in the queue.</typeparam>
#pragma warning disable MEN002
    // This class referenced the implementation of the following.
    // https://github.com/couchcoding/Logbert/blob/bbed28fabf9493310f4b51324f8af88c14551c9d/src/Logbert/Helper/FixedSizedQueue.cs
#pragma warning restore MEN002
    internal class FixedSizedQueue<T> : ConcurrentQueue<T>
    {
        /// <summary>
        /// Simple object for thread synchronization.
        /// </summary>
        private readonly object _syncObject = new object();

        /// <summary>
        /// Creates a new instance of the <see cref="FixedSizedQueue{T}"/>
        /// with the specified <paramref name="size"/>.
        /// </summary>
        /// <param name="size">The maximum size of the <see cref="FixedSizedQueue{T}"/>.</param>
        public FixedSizedQueue(int size)
        {
            Size = size;
        }

        /// <summary>
        /// Gets the fixed size of the <see cref="FixedSizedQueue{T}"/>.
        /// </summary>
        public int Size { get; }

        /// <summary>
        /// Adds an object at the end of the <see cref="FixedSizedQueue{T}"/>.
        /// </summary>
        /// <param name="obj">The object to add at the
        /// end of the <see cref="FixedSizedQueue{T}"/>.</param>
        public new void Enqueue(T obj)
        {
            // Add the object to the queue.
            base.Enqueue(obj);

            lock (_syncObject)
            {
                while (Count > Size)
                {
                    // Ensure we don't exceed the maximum size.
                    TryDequeue(out T _);
                }
            }
        }
    }
}
