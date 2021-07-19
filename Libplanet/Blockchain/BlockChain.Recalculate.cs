using Libplanet.Action;
using Libplanet.Blocks;
using Libplanet.Store;
using System.Collections.Generic;
using System;

namespace Libplanet.Blockchain
{
    public partial class BlockChain<T>
    {
        /// <summary>
        /// Recalculates and rewrites <i>all</i> block states including and upto given
        /// <paramref name="blockHash"/> starting from the genesis block.
        /// </summary>
        /// <param name="blockHash">The inclusive limit of target hash to terminate recalculation.
        /// </param>
        /// <remarks>
        /// If a recalcuation of the entire blockchain is needed, call with the tip hash of the
        /// <see cref="BlockChain{T}"/>.
        /// </remarks>
        internal void RecalculateBlockStates(BlockHash blockHash)
        {
            _logger.Verbose("Recalculating block states upto {BlockHash}...", blockHash);

            // Prevent recursive trial to recalculate & complement incomplete block states by
            // mistake; if the below code works as intended, these state completers must never
            // be invoked.
            StateCompleterSet<T> stateCompleters = StateCompleterSet<T>.Reject;

            foreach (BlockHash hash in BlockHashes)
            {
                Block<T> block = this[hash];
                if (StateStore.ContainsBlockStates(hash))
                {
                    continue;
                }

                IReadOnlyList<ActionEvaluation> evaluations = ActionEvaluator.Evaluate(
                    block,
                    stateCompleters
                );

                _rwlock.EnterWriteLock();
                try
                {
                    SetStates(block, evaluations);
                }
                finally
                {
                    _rwlock.ExitWriteLock();
                }

                if (blockHash.Equals(hash))
                {
                    break;
                }
            }
        }

        /// <summary>
        /// Recalculates and complements all <i>missing</i> block states including and upto given
        /// <paramref name="blockHash"/> starting from the genesis block.
        /// </summary>
        /// <param name="blockHash">The inclusive limit of target hash to terminate complementation.
        /// </param>
        /// <remarks>
        /// <para>
        /// If a complementation of the entire blockchain is needed, call with the tip hash of the
        /// <see cref="BlockChain{T}"/>.
        /// </para>
        /// <para>
        /// Unlike <see cref="RecalculateBlockStates"/>, this method skips recalculations if states
        /// are found for intermediate blocks. Note that this is not fully secure if states for
        /// blocks in <see cref="IStateStore"/> are already corrupted.
        /// </para>
        /// </remarks>
        internal void FullComplementBlockStates(BlockHash blockHash)
        {
            _logger.Verbose("Complementing block states upto {BlockHash}...", blockHash);

            // Prevent recursive trial to recalculate & complement incomplete block states by
            // mistake; if the below code works as intended, these state completers must never
            // be invoked.
            StateCompleterSet<T> stateCompleters = StateCompleterSet<T>.Reject;

            // Calculates and fills the incomplete states on the fly.
            foreach (BlockHash hash in BlockHashes)
            {
                Block<T> block = this[hash];
                if (StateStore.ContainsBlockStates(hash))
                {
                    continue;
                }

                IReadOnlyList<ActionEvaluation> evaluations = ActionEvaluator.Evaluate(
                    block,
                    stateCompleters
                );

                _rwlock.EnterWriteLock();
                try
                {
                    SetStates(block, evaluations);
                }
                finally
                {
                    _rwlock.ExitWriteLock();
                }

                if (blockHash.Equals(hash))
                {
                    break;
                }
            }
        }

        internal void TailComplementBlockStates(BlockHash blockHash)
        {
            throw new NotImplementedException("Placeholder.");
        }
    }
}