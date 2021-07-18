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
        /// Recalculates and complements a block's incomplete states on the fly.
        /// Incomplete states are filled with the recalculated states and the states are
        /// permanently remained in the store.
        /// </summary>
        public static readonly FungibleAssetStateCompleter<T> Recalculate =
            (blockChain, blockHash, address, currency) =>
            {
                blockChain.ComplementBlockStates(blockHash);
                return blockChain.GetBalance(address, currency, blockHash);
            };

        public static readonly FungibleAssetStateCompleter<T> FullComplement =
            (blockChain, blockHash, address, currency) =>
        {
            throw new NotImplementedException("Placeholder.");
        };

        public static readonly FungibleAssetStateCompleter<T> TailComplement =
            (blockChain, blockHash, address, currency) =>
        {
            throw new NotImplementedException("Placeholder.");
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
