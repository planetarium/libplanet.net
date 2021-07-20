#nullable enable
using System;
using Bencodex.Types;
using Libplanet.Action;
using Libplanet.Blocks;

namespace Libplanet.Blockchain
{
    /// <summary>
    /// Predefined built-in state completers that satisfy <see cref="StateCompleter{T}"/> delegate.
    /// </summary>
    /// <typeparam name="T">An <see cref="IAction"/> type.  It should match to
    /// <see cref="BlockChain{T}"/>'s type parameter.</typeparam>
    public static class StateCompleters<T>
        where T : IAction, new()
    {
        /// <summary>
        /// See <see cref="StateCompleterSet{T}.Recalculate"/>.
        /// </summary>
        public static readonly StateCompleter<T> Recalculate = (blockChain, blockHash, address) =>
        {
            blockChain.RecalculateBlockStates(blockHash);
            return blockChain.GetState(address, blockHash);
        };

        /// <summary>
        /// See <see cref="StateCompleterSet{T}.ComplementAll"/>.
        /// </summary>
        public static readonly StateCompleter<T> ComplementAll =
            (blockChain, blockHash, address) =>
        {
            blockChain.ComplementAllBlockStates(blockHash);
            return blockChain.GetState(address, blockHash);
        };

        /// <summary>
        /// See <see cref="StateCompleterSet{T}.ComplementLatest"/>.
        /// </summary>
        public static readonly StateCompleter<T> ComplementLatest =
            (blockChain, blockHash, address) =>
        {
            blockChain.ComplementLatestBlockStates(blockHash);
            return blockChain.GetState(address, blockHash);
        };

        /// <summary>
        /// Rejects to complement incomplete state and throws
        /// an <see cref="IncompleteBlockStatesException"/>.
        /// </summary>
        public static readonly StateCompleter<T> Reject = (chain, blockHash, address) =>
            throw new IncompleteBlockStatesException(blockHash);

        internal static Func<BlockChain<T>, BlockHash, IValue> ToRawStateCompleter(
            StateCompleter<T> stateCompleter,
            Address address
        ) =>
            (blockChain, hash) => stateCompleter(blockChain, hash, address);
    }
}
