using System.Collections.Generic;
using Libplanet.Action;
using Libplanet.Blocks;
using Libplanet.Store;

namespace Libplanet.Blockchain
{
    public partial class BlockChain<T>
    {
        /// <summary>
        /// Recalculates <i>all</i> block states and complements missing states including and upto
        /// given <paramref name="blockHash"/> starting from the genesis block.
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
        /// are found for intermediate blocks. This may not be fully secure if states for
        /// blocks in <see cref="IStateStore"/> are somehow corrupted.
        /// </para>
        /// </remarks>
        internal void ComplementAllBlockStates(BlockHash blockHash)
        {
            _logger.Verbose("Complementing all block states upto {BlockHash}...", blockHash);

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
                    stateCompleters);

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
        /// <paramref name="blockHash"/> starting from the last known states in
        /// <see cref="StateStore"/> before <paramref name="blockHash"/> if the states are missing
        /// for <paramref name="blockHash"/>.
        /// </summary>
        /// <param name="blockHash">The starting point for searching backwards.</param>
        internal void ComplementLatestBlockStates(BlockHash blockHash)
        {
            _logger.Verbose("Complementing latest block states upto {BlockHash}...", blockHash);

            // Prevent recursive trial to recalculate & complement incomplete block states by
            // mistake; if the below code works as intended, these state completers must never
            // be invoked.
            StateCompleterSet<T> stateCompleters = StateCompleterSet<T>.Reject;
            Stack<BlockHash> stack = new Stack<BlockHash>();
            BlockHash? pointer = blockHash;

            while (pointer is { } p)
            {
                if (StateStore.ContainsBlockStates(p))
                {
                    break;
                }
                else
                {
                    stack.Push(p);
                    pointer = this[p].PreviousHash;
                }
            }

            foreach (BlockHash hash in stack)
            {
                Block<T> block = this[hash];
                IReadOnlyList<ActionEvaluation> evaluations = ActionEvaluator.Evaluate(
                    block,
                    stateCompleters);

                _rwlock.EnterWriteLock();
                try
                {
                    SetStates(block, evaluations);
                }
                finally
                {
                    _rwlock.ExitWriteLock();
                }
            }
        }
    }
}
