#nullable enable
using System;
using Bencodex.Types;
using Libplanet.Action;
using Libplanet.Assets;
using Libplanet.Blocks;

namespace Libplanet.Blockchain
{
    /// <summary>
    /// Predefined built-in state completers that satisfy
    /// <see cref="FungibleAssetStateCompleter{T}"/> delegate.
    /// </summary>
    /// <typeparam name="T">An <see cref="IAction"/> type.  It should match to
    /// <see cref="BlockChain{T}"/>'s type parameter.</typeparam>
    public static class FungibleAssetStateCompleters<T>
        where T : IAction, new()
    {
        /// <summary>
        /// See <see cref="StateCompleterSet{T}.Recalculate"/>.
        /// </summary>
        public static readonly FungibleAssetStateCompleter<T> Recalculate =
            (blockChain, blockHash, address, currency) =>
            {
                blockChain.RecalculateBlockStates(blockHash);
                return blockChain.GetBalance(address, currency, blockHash);
            };

        /// <summary>
        /// See <see cref="StateCompleterSet{T}.ComplementAll"/>.
        /// </summary>
        public static readonly FungibleAssetStateCompleter<T> ComplementAll =
            (blockChain, blockHash, address, currency) =>
        {
                blockChain.ComplementAllBlockStates(blockHash);
                return blockChain.GetBalance(address, currency, blockHash);
        };

        /// <summary>
        /// See <see cref="StateCompleterSet{T}.ComplementLatest"/>.
        /// </summary>
        public static readonly FungibleAssetStateCompleter<T> ComplementLatest =
            (blockChain, blockHash, address, currency) =>
        {
                blockChain.ComplementLatestBlockStates(blockHash);
                return blockChain.GetBalance(address, currency, blockHash);
        };

        /// <summary>
        /// Rejects to complement incomplete state and throws
        /// an <see cref="IncompleteBlockStatesException"/>.
        /// </summary>
        public static readonly FungibleAssetStateCompleter<T> Reject =
            (chain, blockHash, address, currency) =>
                throw new IncompleteBlockStatesException(blockHash);

        internal static Func<BlockChain<T>, BlockHash, IValue> ToRawStateCompleter(
            FungibleAssetStateCompleter<T> stateCompleter,
            Address address,
            Currency currency
        ) =>
            (blockChain, hash) =>
            {
                FungibleAssetValue balance = stateCompleter(blockChain, hash, address, currency);
                return (Bencodex.Types.Integer)balance.RawValue;
            };
    }
}
