using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Libplanet.Blockchain;
using Libplanet.Blocks;
using Nito.AsyncEx;

namespace Libplanet.Net
{
    public partial class Swarm<T>
    {
        /// <summary>
        /// Information of <see cref="Swarm{T}"/>'s demand for new blocks.
        /// It is null when the <see cref="Swarm{T}"/> does not have any block to demand.
        /// <seealso cref="BlockDemand"/>
        /// </summary>
        public BlockDemand? BlockDemand { get; private set; }

        internal AsyncAutoResetEvent FillBlocksAsyncStarted { get; } = new AsyncAutoResetEvent();

        internal AsyncAutoResetEvent FillBlocksAsyncFailed { get; } = new AsyncAutoResetEvent();

        internal AsyncAutoResetEvent ProcessFillBlocksFinished { get; } = new AsyncAutoResetEvent();

        private async Task ProcessFillBlocks(
            TimeSpan timeout,
            CancellationToken cancellationToken
        )
        {
            var sessionRandom = new Random();
            IComparer<BlockPerception> canonComparer = BlockChain.Policy.CanonicalChainComparer;
            while (!cancellationToken.IsCancellationRequested)
            {
                int sessionId = sessionRandom.Next();

                if (!(BlockDemand is { } blockDemand))
                {
                    await Task.Delay(1, cancellationToken);
                    continue;
                }

                BoundPeer peer = blockDemand.Peer;

                try
                {
                    if (canonComparer.Compare(
                            BlockChain.PerceiveBlock(BlockDemand?.Header),
                            BlockChain.PerceiveBlock(BlockChain.Tip)
                        ) <= 0)
                    {
                        using (await _blockSyncMutex.LockAsync(cancellationToken))
                        {
                            BlockDemand = null;
                            continue;
                        }
                    }

                    var hash = new BlockHash(blockDemand.Header.Hash);
                    const string startLogMsg =
                        "{SessionId}: Got a new " + nameof(BlockDemand) + " from {Peer}; started " +
                        "to fetch the block #{BlockIndex} {BlockHash}...";
                    _logger.Debug(startLogMsg, sessionId, peer, blockDemand.Header.Index, hash);
                    await SyncPreviousBlocksAsync(
                        blockChain: BlockChain,
                        peer: peer,
                        stop: hash,
                        progress: null,
                        timeout: timeout,
                        totalBlockCount: 0,
                        logSessionId: sessionId,
                        cancellationToken: cancellationToken
                    );
                    _logger.Debug(
                        "{SessionId}: Synced block(s) from {Peer}; broadcast them to neighbors...",
                        sessionId,
                        peer
                    );

                    // FIXME: Clean up events
                    BlockReceived.Set();
                    BlockAppended.Set();
                    BroadcastBlock(peer.Address, BlockChain.Tip);

                    ProcessFillBlocksFinished.Set();
                }
                catch (TimeoutException)
                {
                    const string msg =
                        "{SessionId}: Timeout occurred during " + nameof(ProcessFillBlocks) +
                        "() from {Peer}.";
                    _logger.Debug(msg, sessionId, peer);
                }
                catch (InvalidBlockIndexException ibie)
                {
                    const string msg =
                        "{SessionId}: " + nameof(InvalidBlockIndexException) + " occurred during " +
                        nameof(ProcessFillBlocks) + "() from {Peer}: {Exception}";
                    _logger.Warning(ibie, msg, sessionId, peer, ibie);
                }
                catch (Exception e)
                {
                    const string msg =
                        "{SessionId}: Unexpected exception occurred during " +
                        nameof(ProcessFillBlocks) + "() from {Peer}: {Exception}";
                    _logger.Error(e, msg, sessionId, peer, e);
                }
                finally
                {
                    using (await _blockSyncMutex.LockAsync(cancellationToken))
                    {
                        const string msg =
                            "{SessionId}: " + nameof(ProcessFillBlocks) + "() finished.";
                        _logger.Debug(msg, sessionId);
                        if (BlockDemand.Equals(blockDemand))
                        {
                            const string resetMsg =
                                "{SessionId}: Reset " + nameof(BlockDemand) + "...";
                            _logger.Debug(resetMsg, sessionId);
                            BlockDemand = null;
                        }
                    }
                }
            }
        }

        private async Task SyncPreviousBlocksAsync(
            BlockChain<T> blockChain,
            BoundPeer peer,
            BlockHash? stop,
            IProgress<BlockDownloadState> progress,
            TimeSpan timeout,
            long totalBlockCount,
            int logSessionId,
            CancellationToken cancellationToken
        )
        {
            long previousTipIndex = blockChain.Tip?.Index ?? -1;
            BlockChain<T> synced = null;

            try
            {
                long currentTipIndex = blockChain.Tip?.Index ?? -1;
                long receivedBlockCount = currentTipIndex - previousTipIndex;

                const string startMsg = "{SessionId}: Starts " + nameof(FillBlocksAsync) + "()...";
                _logger.Debug(startMsg, logSessionId);
                FillBlocksAsyncStarted.Set();
                synced = await FillBlocksAsync(
                    peer,
                    blockChain,
                    stop,
                    progress,
                    totalBlockCount,
                    receivedBlockCount,
                    true,
                    timeout,
                    logSessionId,
                    cancellationToken
                );
                const string finishMsg = "{SessionId}: Finished " + nameof(FillBlocksAsync) + "().";
                _logger.Debug(finishMsg, logSessionId);
            }
            catch (Exception)
            {
                FillBlocksAsyncFailed.Set();
                throw;
            }
            finally
            {
                var canonComparer = BlockChain.Policy.CanonicalChainComparer;
                if (synced is { } syncedB
                    && !syncedB.Id.Equals(blockChain?.Id)
                    && (canonComparer.Compare(
                        blockChain.PerceiveBlock(blockChain.Tip),
                        blockChain.PerceiveBlock(syncedB.Tip)) < 0
                    )
                )
                {
                    _logger.Debug(
                        "{SessionId}: Swap the chain {ChainIdA} for the chain {ChainIdB}...",
                        logSessionId,
                        blockChain.Id,
                        synced.Id
                    );
                    blockChain.Swap(
                        synced,
                        render: true,
                        stateCompleters: null
                    );
                    _logger.Debug(
                        "{SessionId}: The chain {ChainIdB} replaced {ChainIdA}",
                        logSessionId,
                        synced.Id,
                        blockChain.Id
                    );
                }
            }
        }

#pragma warning disable MEN003
        private async Task<BlockChain<T>> FillBlocksAsync(
            BoundPeer peer,
            BlockChain<T> blockChain,
            BlockHash? stop,
            IProgress<BlockDownloadState> progress,
            long totalBlockCount,
            long receivedBlockCount,
            bool evaluateActions,
            TimeSpan timeout,
            int logSessionId,
            CancellationToken cancellationToken
        )
        {
            var sessionRandom = new Random();
            const string fname = nameof(FillBlocksAsync);
            BlockChain<T> workspace = blockChain;
            var scope = new List<Guid>();
            bool renderActions = evaluateActions;
            bool renderBlocks = true;

            try
            {
                while (!cancellationToken.IsCancellationRequested)
                {
                    int subSessionId = sessionRandom.Next();
                    Block<T> tip = workspace?.Tip;

                    _logger.Debug(
                        "{SessionId}/{SubSessionId}: Trying to find branchpoint...",
                        logSessionId,
                        subSessionId
                    );
                    BlockLocator locator = workspace.GetBlockLocator(Options.BranchpointThreshold);
                    _logger.Debug(
                        "{SessionId}/{SubSessionId}: Locator's length: {LocatorLength}",
                        logSessionId,
                        subSessionId,
                        locator.Count()
                    );
                    IAsyncEnumerable<Tuple<long, BlockHash>> hashesAsync = GetBlockHashes(
                        peer: peer,
                        locator: locator,
                        stop: stop,
                        timeout: timeout,
                        logSessionIds: (logSessionId, subSessionId),
                        cancellationToken: cancellationToken
                    );
                    IEnumerable<Tuple<long, BlockHash>> hashes =
                        await hashesAsync.ToArrayAsync(cancellationToken);

                    if (!hashes.Any())
                    {
                        _logger.Debug(
                            "{SessionId}/{SubSessionId}: Peer {0} returned no hashes; ignored.",
                            logSessionId,
                            subSessionId,
                            peer.Address.ToHex()
                        );
                        return workspace;
                    }

                    hashes.First().Deconstruct(
                        out long branchIndex,
                        out BlockHash branchpoint
                    );

                    _logger.Debug(
                        "{SessionId}/{SubSessionId}: Branchpoint is #{BranchIndex} {BranchHash}.",
                        logSessionId,
                        subSessionId,
                        branchIndex,
                        branchpoint
                    );

                    if (tip is null || branchpoint.Equals(tip.Hash))
                    {
                        _logger.Debug(
                            "{SessionId}/{SubSessionId}: It doesn't need to fork.",
                            logSessionId,
                            subSessionId
                        );
                    }
                    else if (!workspace.ContainsBlock(branchpoint))
                    {
                        // FIXME: This behavior can unexpectedly terminate the swarm (and the game
                        // app) if it encounters a peer having a different blockchain, and therefore
                        // can be exploited to remotely shut down other nodes as well.
                        // Since the intention of this behavior is to prevent mistakes to try to
                        // connect incorrect seeds (by a user), this behavior should be limited for
                        // only seed peers.
                        var msg =
                            $"Since the genesis block is fixed to {BlockChain.Genesis} " +
                            "protocol-wise, the blockchain which does not share " +
                            "any mutual block is not acceptable.";
                        throw new InvalidGenesisBlockException(
                            branchpoint,
                            workspace.Genesis.Hash,
                            msg);
                    }
                    else
                    {
                        _logger.Debug(
                            "{SessionId}/{SubSessionId}: Needs to fork; trying to fork...",
                            logSessionId,
                            subSessionId
                        );
                        workspace = workspace.Fork(branchpoint);
                        Guid workChainId = workspace.Id;
                        scope.Add(workChainId);
                        renderActions = false;
                        renderBlocks = false;
                        _logger.Debug(
                            "{SessionId}/{SubSessionId}: Fork finished.",
                            logSessionId,
                            subSessionId
                        );
                    }

                    if (!(workspace.Tip is null))
                    {
                        hashes = hashes.Skip(1);
                    }

                    _logger.Debug(
                        "{SessionId}/{SubSessionId}: Trying to fill up previous blocks...",
                        logSessionId,
                        subSessionId
                    );

                    var hashesAsArray = hashes as Tuple<long, BlockHash>[] ?? hashes.ToArray();
                    if (!hashesAsArray.Any())
                    {
                        break;
                    }

                    int hashCount = hashesAsArray.Count();
                    _logger.Debug(
                        "{SessionId}/{SubSessionId}: Required {Hashes} hashes " +
                        "(tip: #{TipIndex} {TipHash}).",
                        logSessionId,
                        subSessionId,
                        hashCount,
                        workspace.Tip?.Index,
                        workspace.Tip?.Hash
                    );

                    totalBlockCount = Math.Max(totalBlockCount, receivedBlockCount + hashCount);

                    IAsyncEnumerable<Block<T>> blocks = GetBlocksAsync(
                        peer,
                        hashesAsArray.Select(pair => pair.Item2),
                        cancellationToken
                    );

                    var receivedBlockCountCurrentLoop = 0;
                    await foreach (Block<T> block in blocks)
                    {
                        const string startMsg =
                            "{SessionId}/{SubSessionId}: Try to append a block " +
                            "#{BlockIndex} {BlockHash}...";
                        _logger.Debug(
                            startMsg,
                            logSessionId,
                            subSessionId,
                            block.Index,
                            block.Hash
                        );

                        cancellationToken.ThrowIfCancellationRequested();

                        workspace.Append(
                            block,
                            DateTimeOffset.UtcNow,
                            evaluateActions: evaluateActions,
                            renderBlocks: renderBlocks,
                            renderActions: renderActions
                        );
                        receivedBlockCountCurrentLoop++;
                        progress?.Report(new BlockDownloadState
                        {
                            TotalBlockCount = totalBlockCount,
                            ReceivedBlockCount = receivedBlockCount + receivedBlockCountCurrentLoop,
                            ReceivedBlockHash = block.Hash,
                            SourcePeer = peer,
                        });
                        const string endMsg =
                            "{SessionId}/{SubSessionId}: Block #{BlockIndex} {BlockHash} " +
                            "was appended.";
                        _logger.Debug(endMsg, logSessionId, subSessionId, block.Index, block.Hash);
                    }

                    receivedBlockCount += receivedBlockCountCurrentLoop;
                    var isEndedFirstTime = receivedBlockCount == receivedBlockCountCurrentLoop &&
                                           receivedBlockCount < FindNextHashesChunkSize - 1;

                    if (receivedBlockCountCurrentLoop < FindNextHashesChunkSize && isEndedFirstTime)
                    {
                        _logger.Debug(
                            "{SessionId}/{SubSessionId}: Got {Blocks} blocks from Peer {Peer} " +
                            "(tip: #{TipIndex} {TipHash})",
                            logSessionId,
                            subSessionId,
                            receivedBlockCountCurrentLoop,
                            peer.Address.ToHex(),
                            workspace.Tip?.Index,
                            workspace.Tip?.Hash
                        );
                        break;
                    }
                }
            }
            catch (Exception e)
            {
                const string msg =
                    "{SessionId}: Unexpected error occurred during " + fname + "(): {Exception}";
                _logger.Error(e, msg, logSessionId, e);
                if (workspace?.Id is Guid workspaceId && scope.Contains(workspaceId))
                {
                    _store.DeleteChainId(workspaceId);
                }

                throw;
            }
            finally
            {
                const string msg =
                    "{SessionId}: " + fname +
                    "() completed (chain ID: {ChainId}, tip: #{TipIndex} {TipHash}).";
                _logger.Debug(
                    msg,
                    logSessionId,
                    workspace?.Id,
                    workspace?.Tip?.Index,
                    workspace?.Tip?.Hash
                );
                foreach (var id in scope.Where(guid => guid != workspace?.Id))
                {
                    _store.DeleteChainId(id);
                }
            }

            return workspace;
        }
#pragma warning restore MEN003
    }
}
