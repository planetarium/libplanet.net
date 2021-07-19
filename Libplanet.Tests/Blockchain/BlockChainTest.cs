using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Security.Cryptography;
using System.Threading.Tasks;
using Bencodex.Types;
using Libplanet.Action;
using Libplanet.Assets;
using Libplanet.Blockchain;
using Libplanet.Blockchain.Policies;
using Libplanet.Blockchain.Renderers;
using Libplanet.Blockchain.Renderers.Debug;
using Libplanet.Blocks;
using Libplanet.Crypto;
using Libplanet.Store;
using Libplanet.Tests.Action;
using Libplanet.Tests.Blocks;
using Libplanet.Tests.Common.Action;
using Libplanet.Tests.Store;
using Libplanet.Tests.Store.Trie;
using Libplanet.Tx;
using Serilog;
using Serilog.Events;
using Xunit;
using Xunit.Abstractions;
using static Libplanet.Tests.Common.Action.ThrowException;

namespace Libplanet.Tests.Blockchain
{
    public partial class BlockChainTest : IDisposable
    {
        private readonly ILogger _logger;
        private StoreFixture _fx;
        private BlockPolicy<DumbAction> _policy;
        private BlockChain<DumbAction> _blockChain;
        private ValidatingActionRenderer<DumbAction> _renderer;
        private Block<DumbAction> _validNext;
        private List<Transaction<DumbAction>> _emptyTransaction;
        private IStagePolicy<DumbAction> _stagePolicy;

        public BlockChainTest(ITestOutputHelper output)
        {
            Log.Logger = _logger = new LoggerConfiguration()
                .MinimumLevel.Verbose()
                .Enrich.WithThreadId()
                .WriteTo.TestOutput(output)
                .CreateLogger()
                .ForContext<BlockChainTest>();

            _policy = new BlockPolicy<DumbAction>(new MinerReward(1), maxBlockBytes: 50 * 1024);
            _stagePolicy = new VolatileStagePolicy<DumbAction>();
            _fx = new DefaultStoreFixture(memory: true, blockAction: _policy.BlockAction);
            _renderer = new ValidatingActionRenderer<DumbAction>();
            _blockChain = new BlockChain<DumbAction>(
                _policy,
                _stagePolicy,
                _fx.Store,
                _fx.StateStore,
                _fx.GenesisBlock,
                renderers: new[] { new LoggedActionRenderer<DumbAction>(_renderer, Log.Logger) }
            );
            _renderer.BlockChain = _blockChain;
            _renderer.ResetRecords();

            _emptyTransaction = new List<Transaction<DumbAction>>();
            _validNext = Block<DumbAction>.Mine(
                1,
                _policy.GetHashAlgorithm(1),
                1024,
                _fx.GenesisBlock.TotalDifficulty,
                _fx.GenesisBlock.Miner,
                _fx.GenesisBlock.Hash,
                _fx.GenesisBlock.Timestamp.AddSeconds(1),
                _emptyTransaction
            ).AttachStateRootHash(_fx.StateStore, _policy);
        }

        public void Dispose()
        {
            _fx.Dispose();
        }

        [Fact]
        public void PerceiveBlock()
        {
            var blockA = new SimpleBlockExcerpt()
            {
                ProtocolVersion = BlockHeader.CurrentProtocolVersion,
                Index = 604665,
                Hash = BlockHash.FromString(
                    "4f612467ed79cb854d1901f131ccfc8a40bba89651e1a9e1dcea1287dd70d8ee"),
                TotalDifficulty = 21584091240753,
            };

            DateTimeOffset timeA = DateTimeOffset.FromUnixTimeSeconds(1609426800);
            BlockPerception perceptionA = _blockChain.PerceiveBlock(blockA, timeA);
            Assert.Equal(blockA, perceptionA.BlockExcerpt);
            Assert.Equal(timeA, perceptionA.PerceivedTime);

            perceptionA = _blockChain.PerceiveBlock(blockA);
            Assert.Equal(blockA, perceptionA.BlockExcerpt);
            Assert.Equal(timeA, perceptionA.PerceivedTime);

            var blockB = new SimpleBlockExcerpt
            {
                ProtocolVersion = BlockHeader.CurrentProtocolVersion,
                Index = 604664,
                Hash = BlockHash.FromString(
                    "9a87556f3198d8bd48300d2a6a5957d661c760a7fb72ef4a4b8c01c155b77e99"),
                TotalDifficulty = 21584061959429,
            };

            DateTimeOffset timeBMin = DateTimeOffset.UtcNow;
            BlockPerception perceptionB = _blockChain.PerceiveBlock(blockB);
            DateTimeOffset timeBMax = DateTimeOffset.UtcNow;
            Assert.Equal(blockB, perceptionB.BlockExcerpt);
            Assert.InRange(perceptionB.PerceivedTime, timeBMin, timeBMax);

            DateTimeOffset timeB = perceptionB.PerceivedTime;
            perceptionB = _blockChain.PerceiveBlock(blockB);
            Assert.Equal(blockB, perceptionB.BlockExcerpt);
            Assert.Equal(timeB, perceptionB.PerceivedTime);
        }

        [Fact]
        public async void CanFindBlockByIndex()
        {
            var genesis = _blockChain.Genesis;
            Assert.Equal(genesis, _blockChain[0]);

            Block<DumbAction> block = await _blockChain.MineBlock(_fx.Address2);
            Assert.Equal(block, _blockChain[1]);
        }

        [Fact]
        public async void CanonicalId()
        {
            var x = _blockChain;
            await x.MineBlock(_fx.Address1);
            await x.MineBlock(_fx.Address1);
            Assert.Equal(x.Id, _fx.Store.GetCanonicalChainId());
            var y = x.Fork(x.Tip.Hash);
            await y.MineBlock(_fx.Address1);
            Assert.Equal(x.Id, _fx.Store.GetCanonicalChainId());

            var z = new BlockChain<DumbAction>(
                new BlockPolicy<DumbAction>(new MinerReward(1)),
                new VolatileStagePolicy<DumbAction>(),
                _fx.Store,
                _fx.StateStore,
                _fx.GenesisBlock
            );

            Assert.Equal(x.Id, z.Id);
        }

        [Fact]
        public async void BlockHashes()
        {
            var genesis = _blockChain.Genesis;

            Assert.Single(_blockChain.BlockHashes);

            Block<DumbAction> b1 = await _blockChain.MineBlock(_fx.Address1);
            Assert.Equal(new[] { genesis.Hash, b1.Hash }, _blockChain.BlockHashes);

            Block<DumbAction> b2 = await _blockChain.MineBlock(_fx.Address1);
            Assert.Equal(
                new[] { genesis.Hash, b1.Hash, b2.Hash },
                _blockChain.BlockHashes
            );

            Block<DumbAction> b3 = await _blockChain.MineBlock(_fx.Address1);
            Assert.Equal(
                new[] { genesis.Hash, b1.Hash, b2.Hash, b3.Hash },
                _blockChain.BlockHashes
            );
        }

        [Fact]
        public async void ProcessActions()
        {
            HashAlgorithmType hashAlgorithm = HashAlgorithmType.Of<SHA256>();
            Block<PolymorphicAction<BaseAction>> genesisBlock =
                BlockChain<PolymorphicAction<BaseAction>>.MakeGenesisBlock(hashAlgorithm);
            var store = new DefaultStore(path: null);
            var stateStore =
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore());
            var chain = new BlockChain<PolymorphicAction<BaseAction>>(
                new BlockPolicy<PolymorphicAction<BaseAction>>(),
                new VolatileStagePolicy<PolymorphicAction<BaseAction>>(),
                store,
                stateStore,
                genesisBlock
            );

            var actions1 = new List<PolymorphicAction<BaseAction>>
            {
                new Attack
                {
                    Weapon = "sword",
                    Target = "goblin",
                    TargetAddress = _fx.Address1,
                },
                new Attack
                {
                    Weapon = "sword",
                    Target = "orc",
                    TargetAddress = _fx.Address1,
                },
                new Attack
                {
                    Weapon = "staff",
                    Target = "goblin",
                    TargetAddress = _fx.Address1,
                },
            };
            var tx1 = Transaction<PolymorphicAction<BaseAction>>.Create(
                0,
                new PrivateKey(),
                genesisBlock.Hash,
                actions1
            );

            chain.StageTransaction(tx1);
            await chain.MineBlock(_fx.Address1);

            IValue state = chain.GetState(_fx.Address1);
            Assert.NotNull(state);

            var result = BattleResult.FromBencodex((Bencodex.Types.Dictionary)state);
            Assert.Contains("sword", result.UsedWeapons);
            Assert.Contains("staff", result.UsedWeapons);
            Assert.Contains("orc", result.Targets);
            Assert.Contains("goblin", result.Targets);

            PolymorphicAction<BaseAction>[] actions2 =
            {
                new Attack
                {
                    Weapon = "bow",
                    Target = "goblin",
                    TargetAddress = _fx.Address1,
                },
            };
            var tx2 = Transaction<PolymorphicAction<BaseAction>>.Create(
                0,
                new PrivateKey(),
                genesisBlock.Hash,
                actions2
            );

            chain.StageTransaction(tx2);
            await chain.MineBlock(_fx.Address1);

            state = chain.GetState(_fx.Address1);
            result = BattleResult.FromBencodex((Bencodex.Types.Dictionary)state);
            Assert.Contains("bow", result.UsedWeapons);

            var tx3 = Transaction<PolymorphicAction<BaseAction>>.Create(
                0,
                new PrivateKey(),
                genesisBlock.Hash,
                new List<PolymorphicAction<BaseAction>>
                {
                    new Attack
                    {
                        Weapon = "sword",
                        Target = "orc",
                        TargetAddress = _fx.Address1,
                    },
                }
            );
            chain.StageTransaction(tx3);
            await chain.MineBlock(_fx.Address1);
            state = chain.GetState(_fx.Address1);

            Assert.NotNull(state);
        }

        [Fact]
        public void ShortCircuitActionEvaluationForUnrenderWithNoActionRenderers()
        {
            IEnumerable<ExecuteRecord> NonRehearsalExecutions() =>
                DumbAction.ExecuteRecords.Value.Where(r => !r.Rehearsal);

            var policy = new BlockPolicy<DumbAction>();
            var key = new PrivateKey();
            Address miner = key.ToAddress();

            using (var fx = new DefaultStoreFixture(memory: true))
            {
                var emptyRenderer = new AnonymousRenderer<DumbAction>();
                var chain = new BlockChain<DumbAction>(
                    policy,
                    new VolatileStagePolicy<DumbAction>(),
                    fx.Store,
                    fx.StateStore,
                    fx.GenesisBlock,
                    renderers: new[] { emptyRenderer }
                );
                var actions = new[] { new DumbAction(miner, "foo") };
                var tx = chain.MakeTransaction(key, actions);
                var block = TestUtils.MineNext(
                    chain.Genesis,
                    policy.GetHashAlgorithm,
                    new[] { tx },
                    miner: miner,
                    difficulty: policy.GetNextBlockDifficulty(_blockChain)
                ).AttachStateRootHash(fx.StateStore, policy);
                chain.Append(block);
                var forked = chain.Fork(chain.Genesis.Hash);
                forked.Append(block);

                DumbAction.ExecuteRecords.Value = ImmutableList<ExecuteRecord>.Empty;
                Assert.Empty(DumbAction.ExecuteRecords.Value);

                // Stale actions shouldn't be evaluated because the "renderer" here is not an
                // IActionRenderer<T> but a vanilla IRenderer<T> which means they don't have to
                // be unrendered.
                var renderer = new RecordingActionRenderer<DumbAction>();
                var newChain = new BlockChain<DumbAction>(
                    policy,
                    new VolatileStagePolicy<DumbAction>(),
                    fx.Store,
                    fx.StateStore,
                    Guid.NewGuid(),
                    fx.GenesisBlock,
                    renderers: new[] { renderer }
                );
                chain.Swap(newChain, true);
                Assert.Empty(renderer.ActionRecords);
                Assert.Empty(NonRehearsalExecutions());
            }
        }

        [Fact]
        public async Task ActionRenderersHaveDistinctContexts()
        {
            var policy = new NullPolicy<DumbAction>();
            var store = new DefaultStore(null);
            var stateStore =
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore());
            var generatedRandomValueLogs = new List<int>();
            IActionRenderer<DumbAction>[] renderers = Enumerable.Range(0, 2).Select(i =>
                new LoggedActionRenderer<DumbAction>(
                    new AnonymousActionRenderer<DumbAction>
                    {
                        ActionRenderer = (act, context, nextStates) =>
                            // Consuming the random state through IRandom.Next() should not
                            // affect contexts passed to other action renderers.
                            generatedRandomValueLogs.Add(context.Random.Next()),
                    },
                    Log.Logger.ForContext("RendererIndex", i)
                )
            ).ToArray();
            BlockChain<DumbAction> blockChain = TestUtils.MakeBlockChain(
                policy,
                store,
                stateStore,
                renderers: renderers
            );
            var privateKey = new PrivateKey();
            var action = new DumbAction(default, string.Empty);
            var actions = new[] { action };
            blockChain.MakeTransaction(privateKey, actions);
            Block<DumbAction> block = await blockChain.MineBlock(_fx.Address1, append: false);

            generatedRandomValueLogs.Clear();
            Assert.Empty(generatedRandomValueLogs);
            blockChain.Append(block);
            Assert.Equal(2, generatedRandomValueLogs.Count);
            Assert.Equal(generatedRandomValueLogs[0], generatedRandomValueLogs[1]);
        }

        [Fact]
        public async Task RenderActionsAfterBlockIsRendered()
        {
            var policy = new NullPolicy<DumbAction>();
            var store = new DefaultStore(null);
            var stateStore =
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore());
            var recordingRenderer = new RecordingActionRenderer<DumbAction>();
            var renderer = new LoggedActionRenderer<DumbAction>(recordingRenderer, Log.Logger);
            BlockChain<DumbAction> blockChain =
                TestUtils.MakeBlockChain(policy, store, stateStore, renderers: new[] { renderer });
            var privateKey = new PrivateKey();

            var action = new DumbAction(default, string.Empty);
            var actions = new[] { action };
            blockChain.MakeTransaction(privateKey, actions);
            recordingRenderer.ResetRecords();
            Block<DumbAction> prevBlock = blockChain.Tip;
            Block<DumbAction> block = await blockChain.MineBlock(_fx.Address1);

            Assert.Equal(2, blockChain.Count);
            Assert.Empty(recordingRenderer.ReorgRecords);
            IReadOnlyList<RenderRecord<DumbAction>.Block> blockLogs =
                recordingRenderer.BlockRecords;
            Assert.Equal(2, blockLogs.Count);
            IReadOnlyList<RenderRecord<DumbAction>.ActionBase> actionLogs =
                recordingRenderer.ActionRecords;
            Assert.Single(actions);
            Assert.Equal(prevBlock, blockLogs[0].OldTip);
            Assert.Equal(block, blockLogs[0].NewTip);
            Assert.Equal(0, blockLogs[0].Index);
            Assert.Equal(1, actionLogs[0].Index);
            Assert.Equal(action, actionLogs[0].Action);
            Assert.Equal(prevBlock, blockLogs[1].OldTip);
            Assert.Equal(block, blockLogs[1].NewTip);
            Assert.Equal(2, blockLogs[1].Index);
        }

        [Fact]
        public async Task RenderActionsAfterAppendComplete()
        {
            var policy = new NullPolicy<DumbAction>();
            var store = new DefaultStore(null);
            var stateStore =
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore());
            IActionRenderer<DumbAction> renderer = new AnonymousActionRenderer<DumbAction>
            {
                ActionRenderer = (_, __, nextStates) =>
                    throw new SomeException("thrown by renderer"),
            };
            renderer = new LoggedActionRenderer<DumbAction>(renderer, Log.Logger);
            BlockChain<DumbAction> blockChain =
                TestUtils.MakeBlockChain(policy, store, stateStore, renderers: new[] { renderer });
            var privateKey = new PrivateKey();

            var action = new DumbAction(default, string.Empty);
            var actions = new[] { action };
            blockChain.MakeTransaction(privateKey, actions);

            SomeException e = await Assert.ThrowsAsync<SomeException>(
                async () => await blockChain.MineBlock(_fx.Address1)
            );
            Assert.Equal("thrown by renderer", e.Message);
            Assert.Equal(2, blockChain.Count);
        }

        [Fact]
        public async void FindNextHashes()
        {
            long? offsetIndex;
            IReadOnlyList<BlockHash> hashes;

            _blockChain.FindNextHashes(new BlockLocator(new BlockHash[] { }))
                .Deconstruct(out offsetIndex, out hashes);
            Assert.Single(hashes);
            var block0 = _blockChain.Genesis;
            var block1 = await _blockChain.MineBlock(_fx.Address1);
            var block2 = await _blockChain.MineBlock(_fx.Address1);
            var block3 = await _blockChain.MineBlock(_fx.Address1);

            _blockChain.FindNextHashes(new BlockLocator(new[] { block0.Hash }))
                .Deconstruct(out offsetIndex, out hashes);
            Assert.Equal(0, offsetIndex);
            Assert.Equal(new[] { block0.Hash, block1.Hash, block2.Hash, block3.Hash }, hashes);

            _blockChain.FindNextHashes(new BlockLocator(new[] { block1.Hash, block0.Hash }))
                .Deconstruct(out offsetIndex, out hashes);
            Assert.Equal(1, offsetIndex);
            Assert.Equal(new[] { block1.Hash, block2.Hash, block3.Hash }, hashes);

            _blockChain.FindNextHashes(new BlockLocator(new[] { block0.Hash }), stop: block2.Hash)
                .Deconstruct(out offsetIndex, out hashes);
            Assert.Equal(0, offsetIndex);
            Assert.Equal(new[] { block0.Hash, block1.Hash, block2.Hash }, hashes);

            _blockChain.FindNextHashes(new BlockLocator(new[] { block0.Hash }), count: 2)
                .Deconstruct(out offsetIndex, out hashes);
            Assert.Equal(0, offsetIndex);
            Assert.Equal(new[] { block0.Hash, block1.Hash }, hashes);
        }

        [Fact]
        public async void FindNextHashesAfterFork()
        {
            await _blockChain.MineBlock(_fx.Address1);
            await _blockChain.MineBlock(_fx.Address1);
            await _blockChain.MineBlock(_fx.Address1);

            BlockChain<DumbAction> forked = _blockChain.Fork(_blockChain.Genesis.Hash);
            await forked.MineBlock(_fx.Address1);

            BlockLocator locator = _blockChain.GetBlockLocator();
            forked.FindNextHashes(locator)
                .Deconstruct(out long? offset, out IReadOnlyList<BlockHash> hashes);

            Assert.Equal(forked[0].Index, offset);
            Assert.Equal(new[] { forked[0].Hash, forked[1].Hash }, hashes);
        }

        [Fact]
        public async void Fork()
        {
            var block1 = await _blockChain.MineBlock(_fx.Address1);
            var block2 = await _blockChain.MineBlock(_fx.Address1);
            var block3 = await _blockChain.MineBlock(_fx.Address1);

            BlockChain<DumbAction> forked = _blockChain.Fork(block2.Hash);

            Assert.Equal(
                new[] { block1, block2, block3 },
                new[] { _blockChain[1], _blockChain[2], _blockChain[3] }
            );
            Assert.Equal(4, _blockChain.Count);

            Assert.Equal(
                new[] { block1, block2 },
                new[] { forked[1], forked[2] }
            );
            Assert.Equal(3, forked.Count);
        }

        [Fact]
        public async Task ForkWithBlockNotExistInChain()
        {
            var genesis = await _blockChain.MineBlock(_fx.Address1);

            for (var i = 0; i < 2; i++)
            {
                await _blockChain.MineBlock(_fx.Address1);
            }

            var newBlock = TestUtils.MineNext(genesis, _policy.GetHashAlgorithm, difficulty: 1024);

            Assert.Throws<ArgumentException>(() =>
                _blockChain.Fork(newBlock.Hash));

            _blockChain.Store.PutBlock(newBlock);
            Assert.Throws<ArgumentException>(() =>
                _blockChain.Fork(newBlock.Hash));
        }

        [Fact]
        public void ForkChainWithIncompleteBlockStates()
        {
            (_, _, BlockChain<DumbAction> chain) = MakeIncompleteBlockStates();
            BlockChain<DumbAction> forked = chain.Fork(chain[5].Hash);
            Assert.Equal(chain[5], forked.Tip);
            Assert.Equal(6, forked.Count);
        }

        [Fact]
        public async Task StateAfterForkingAndAddingExistingBlock()
        {
            var miner = _fx.Address1;
            var privateKey = new PrivateKey();
            var address = privateKey.ToAddress();
            var actions1 = new[] { new DumbAction(address, "foo") };
            var actions2 = new[] { new DumbAction(address, "bar") };

            _blockChain.MakeTransaction(privateKey, actions1);
            var b1 = await _blockChain.MineBlock(miner);

            _blockChain.MakeTransaction(privateKey, actions2);
            var b2 = await _blockChain.MineBlock(miner);
            var state = _blockChain.GetState(address);

            Assert.Equal((Text)"foo,bar", state);

            var forked = _blockChain.Fork(b1.Hash);
            state = forked.GetState(address);
            Assert.Equal((Text)"foo", state);

            forked.Append(b2);
            state = forked.GetState(address);
            Assert.Equal((Text)"foo,bar", state);
        }

        [Fact]
        public async Task ForkShouldSkipExecuteAndRenderGenesis()
        {
            Address stateKey = _fx.Address1;
            Address miner = _fx.Address2;
            var action = new DumbAction(stateKey, "genesis");

            using (var store = new DefaultStore(null))
            using (var stateStore = new TrieStateStore(
                new MemoryKeyValueStore(), new MemoryKeyValueStore()))
            {
                var genesis = TestUtils.MineGenesis(
                    _policy.GetHashAlgorithm,
                    transactions: new[] { _fx.MakeTransaction(new[] { action }) }
                ).AttachStateRootHash(stateStore, _policy);
                store.PutBlock(genesis);
                var renderer = new RecordingActionRenderer<DumbAction>();
                var blockChain = new BlockChain<DumbAction>(
                    _policy,
                    new VolatileStagePolicy<DumbAction>(),
                    store,
                    stateStore,
                    genesis,
                    renderers: new[] { renderer }
                );

                Assert.Equal(1, renderer.ActionRecords.Count(r => r.Action is DumbAction));
                Assert.Equal(2, renderer.BlockRecords.Count);
                // NOTE: AttachStateRootHash, Append
                Assert.Equal(2, DumbAction.ExecuteRecords.Value.Count(r => !r.Rehearsal));

                await blockChain.MineBlock(miner, DateTimeOffset.UtcNow);
                await blockChain.MineBlock(miner, DateTimeOffset.UtcNow);

                int blockRecordsBeforeFork = renderer.BlockRecords.Count;

                blockChain.Fork(blockChain.Tip.Hash);

                Assert.Equal(1, renderer.ActionRecords.Count(r => r.Action is DumbAction));
                Assert.Equal(blockRecordsBeforeFork, renderer.BlockRecords.Count);
                // NOTE: AttachStateRootHash, Append
                Assert.Equal(2, DumbAction.ExecuteRecords.Value.Count(r => !r.Rehearsal));
            }
        }

        [Fact]
        public void DetectInvalidTxNonce()
        {
            var privateKey = new PrivateKey();
            var actions = new[] { new DumbAction(_fx.Address1, "foo") };

            var genesis = _blockChain.Genesis;

            Transaction<DumbAction>[] txsA =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey),
            };

            Block<DumbAction> b1 = TestUtils.MineNext(
                genesis,
                _policy.GetHashAlgorithm,
                txsA,
                null,
                _policy.GetNextBlockDifficulty(_blockChain),
                blockInterval: TimeSpan.FromSeconds(10))
            .AttachStateRootHash(_fx.StateStore, _policy);
            _blockChain.Append(b1);

            Block<DumbAction> b2 = TestUtils.MineNext(
                b1,
                _policy.GetHashAlgorithm,
                txsA,
                null,
                _policy.GetNextBlockDifficulty(_blockChain),
                blockInterval: TimeSpan.FromSeconds(10)
            ).AttachStateRootHash(_fx.StateStore, _policy);
            Assert.Throws<InvalidTxNonceException>(() =>
                _blockChain.Append(b2));

            Transaction<DumbAction>[] txsB =
            {
                _fx.MakeTransaction(
                    actions,
                    nonce: 1,
                    privateKey: privateKey),
            };
            b2 = TestUtils.MineNext(
                b1,
                _policy.GetHashAlgorithm,
                txsB,
                null,
                _policy.GetNextBlockDifficulty(_blockChain),
                blockInterval: TimeSpan.FromSeconds(10)
            ).AttachStateRootHash(_fx.StateStore, _policy);
            _blockChain.Append(b2);
        }

        [Fact]
        public void ForkTxNonce()
        {
            // An active account, so that its some recent transactions became "stale" due to a fork.
            var privateKey = new PrivateKey();
            Address address = privateKey.ToAddress();

            // An inactive account, so that it has no recent transactions but only an old
            // transaction, so that its all transactions are stale-proof (stale-resistant).
            var lessActivePrivateKey = new PrivateKey();
            Address lessActiveAddress = lessActivePrivateKey.ToAddress();

            var actions = new[] { new DumbAction(address, "foo") };
            HashAlgorithmType hashAlgorithm = HashAlgorithmType.Of<SHA256>();

            var genesis = _blockChain.Genesis;

            Transaction<DumbAction>[] txsA =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey),
                _fx.MakeTransaction(privateKey: lessActivePrivateKey),
            };

            Assert.Equal(0, _blockChain.GetNextTxNonce(address));

            Block<DumbAction> b1 = TestUtils.MineNext(
                genesis,
                _policy.GetHashAlgorithm,
                txsA,
                null,
                _blockChain.Policy.GetNextBlockDifficulty(_blockChain),
                blockInterval: TimeSpan.FromSeconds(10)
            ).AttachStateRootHash(_fx.StateStore, _policy);

            _blockChain.Append(b1);

            Assert.Equal(1, _blockChain.GetNextTxNonce(address));

            Transaction<DumbAction>[] txsB =
            {
                _fx.MakeTransaction(
                    actions,
                    nonce: 1,
                    privateKey: privateKey),
            };
            Block<DumbAction> b2 = TestUtils.MineNext(
                b1,
                _policy.GetHashAlgorithm,
                txsB,
                null,
                _policy.GetNextBlockDifficulty(_blockChain),
                blockInterval: TimeSpan.FromSeconds(10))
            .AttachStateRootHash(_fx.StateStore, _policy);
            _blockChain.Append(b2);

            Assert.Equal(2, _blockChain.GetNextTxNonce(address));

            BlockChain<DumbAction> forked = _blockChain.Fork(b1.Hash);
            Assert.Equal(1, forked.GetNextTxNonce(address));
            Assert.Equal(1, forked.GetNextTxNonce(lessActiveAddress));
        }

        [Fact]
        public async void GetBlockLocator()
        {
            List<Block<DumbAction>> blocks = new List<Block<DumbAction>>();
            foreach (var i in Enumerable.Range(0, 10))
            {
                var block = await _blockChain.MineBlock(_fx.Address1);
                blocks.Add(block);
            }

            BlockLocator actual = _blockChain.GetBlockLocator(threshold: 3);
            BlockLocator expected = new BlockLocator(new[]
            {
                blocks[9].Hash,
                blocks[8].Hash,
                blocks[7].Hash,
                blocks[6].Hash,
                blocks[4].Hash,
                blocks[0].Hash,
                _blockChain.Genesis.Hash,
            });

            Assert.Equal(expected, actual);
        }

        [Theory]
        [InlineData(true)]
        [InlineData(false)]
        public void Swap(bool render)
        {
            Assert.Throws<ArgumentNullException>(() => _blockChain.Swap(null, render));

            (var addresses, Transaction<DumbAction>[] txs1) =
                MakeFixturesForAppendTests();
            var genesis = _blockChain.Genesis;
            var minerAddress = addresses[4];

            Block<DumbAction> block1 = TestUtils.MineNext(
                genesis,
                _policy.GetHashAlgorithm,
                txs1,
                miner: minerAddress,
                difficulty: _policy.GetNextBlockDifficulty(_blockChain),
                blockInterval: TimeSpan.FromSeconds(10)
            ).AttachStateRootHash(_fx.StateStore, _policy);
            _blockChain.Append(block1);

            PrivateKey privateKey = new PrivateKey(new byte[]
            {
                0xa8, 0x21, 0xc7, 0xc2, 0x08, 0xa9, 0x1e, 0x53, 0xbb, 0xb2,
                0x71, 0x15, 0xf4, 0x23, 0x5d, 0x82, 0x33, 0x44, 0xd1, 0x16,
                0x82, 0x04, 0x13, 0xb6, 0x30, 0xe7, 0x96, 0x4f, 0x22, 0xe0,
                0xec, 0xe0,
            });

            BlockChain<DumbAction> fork =
                _blockChain.Fork(_blockChain.Tip.Hash);

            Transaction<DumbAction>[][] txsA =
            {
                new[]
                {
                    _fx.MakeTransaction(
                        new[]
                        {
                            new DumbAction(addresses[0], "foo"),
                        },
                        timestamp: DateTimeOffset.MinValue,
                        nonce: 2,
                        privateKey: privateKey),
                    _fx.MakeTransaction(
                        new[]
                        {
                            new DumbAction(addresses[1], "bar"),
                        },
                        timestamp: DateTimeOffset.MinValue.AddSeconds(3),
                        nonce: 3,
                        privateKey: privateKey),
                },
                new[]
                {
                    _fx.MakeTransaction(
                        new[]
                        {
                            new DumbAction(addresses[2], "baz"),
                        },
                        timestamp: DateTimeOffset.MinValue,
                        nonce: 4,
                        privateKey: privateKey),
                    _fx.MakeTransaction(
                        new[]
                        {
                            new DumbAction(addresses[3], "qux"),
                        },
                        timestamp: DateTimeOffset.MinValue.AddSeconds(4),
                        nonce: 5,
                        privateKey: privateKey),
                },
            };

            foreach (Transaction<DumbAction>[] txs in txsA)
            {
                Block<DumbAction> b = TestUtils.MineNext(
                    _blockChain.Tip,
                    _policy.GetHashAlgorithm,
                    txs,
                    null,
                    _policy.GetNextBlockDifficulty(_blockChain),
                    blockInterval: TimeSpan.FromSeconds(10)
                ).AttachStateRootHash(_fx.StateStore, _policy);
                _blockChain.Append(b);
            }

            Transaction<DumbAction>[] txsB =
            {
                _fx.MakeTransaction(
                    new[]
                    {
                        new DumbAction(addresses[0], "fork-foo"),
                    },
                    timestamp: DateTimeOffset.MinValue,
                    nonce: 2,
                    privateKey: privateKey),
                _fx.MakeTransaction(
                    new[]
                    {
                        new DumbAction(addresses[1], "fork-bar"),
                        new DumbAction(addresses[2], "fork-baz"),
                    },
                    timestamp: DateTimeOffset.MinValue.AddSeconds(2),
                    nonce: 3,
                    privateKey: privateKey),
            };

            Block<DumbAction> forkTip = TestUtils.MineNext(
                fork.Tip,
                _policy.GetHashAlgorithm,
                txsB,
                null,
                _policy.GetNextBlockDifficulty(_blockChain),
                blockInterval: TimeSpan.FromSeconds(10)
            ).AttachStateRootHash(_fx.StateStore, _policy);
            fork.Append(
                forkTip,
                DateTimeOffset.UtcNow,
                evaluateActions: true,
                renderBlocks: true,
                renderActions: false
            );

            Guid previousChainId = _blockChain.Id;
            _renderer.ResetRecords();
            _blockChain.Swap(fork, render);

            Assert.Empty(_blockChain.Store.IterateIndexes(previousChainId));
            Assert.Empty(_blockChain.Store.ListTxNonces(previousChainId));

            RenderRecord<DumbAction>.BlockBase[] blockLevelRenders = _renderer.Records
                .OfType<RenderRecord<DumbAction>.BlockBase>()
                .ToArray();

            RenderRecord<DumbAction>.ActionBase[] actionRenders = _renderer.ActionRecords
                .Where(r => r.Action is DumbAction)
                .ToArray();
            DumbAction[] actions = actionRenders.Select(r => (DumbAction)r.Action).ToArray();

            int actionsCountA = txsA.Sum(
                a => a.Sum(tx => tx.Actions.Count)
            );
            int actionsCountB = txsB.Sum(tx => tx.Actions.Count);

            int totalBlockCount = (int)_blockChain[-1].Index + 1;
            int unRenderBlockCount = 2;

            if (render)
            {
                Assert.Equal(4, blockLevelRenders.Length);
                Assert.IsType<RenderRecord<DumbAction>.Reorg>(blockLevelRenders[0]);
                Assert.True(blockLevelRenders[0].Begin);
                Assert.IsType<RenderRecord<DumbAction>.Block>(blockLevelRenders[1]);
                Assert.True(blockLevelRenders[1].Begin);
                Assert.IsType<RenderRecord<DumbAction>.Block>(blockLevelRenders[2]);
                Assert.True(blockLevelRenders[2].End);

                Assert.IsType<RenderRecord<DumbAction>.Reorg>(blockLevelRenders.Last());
                Assert.True(blockLevelRenders.Last().End);

                Assert.True(blockLevelRenders[0].Index < actionRenders[0].Index);
                Assert.True(actionRenders.Last(r => r.Unrender).Index < blockLevelRenders[1].Index);
                Assert.True(blockLevelRenders[1].Index < actionRenders.First(r => r.Render).Index);
                Assert.True(actionRenders.Last().Index < blockLevelRenders[2].Index);

                Assert.Equal(actionsCountB + actionsCountA, actionRenders.Length);
                Assert.True(actionRenders.Take(actionsCountA).All(r => r.Unrender));
                Assert.True(actionRenders.Skip(actionsCountA).All(r => r.Render));

                Assert.Equal("qux", actions[0].Item);
                Assert.Equal("baz", actions[1].Item);
                Assert.Equal("bar", actions[2].Item);
                Assert.Equal("foo", actions[3].Item);
                Assert.Equal("fork-foo", actions[4].Item);
                Assert.Equal("fork-bar", actions[5].Item);
                Assert.Equal("fork-baz", actions[6].Item);

                RenderRecord<DumbAction>.ActionBase[] blockActionRenders = _renderer.ActionRecords
                    .Where(r => r.Action is MinerReward)
                    .ToArray();

                // except genesis block.
                Assert.Equal(
                    (Integer)(totalBlockCount - 1),
                    (Integer)_blockChain.GetState(minerAddress)
                );
                Assert.Equal(totalBlockCount, blockActionRenders.Length);
                Assert.True(blockActionRenders.Take(unRenderBlockCount).All(r => r.Unrender));
                Assert.True(blockActionRenders.Skip(unRenderBlockCount).All(r => r.Render));
            }
            else
            {
                Assert.Empty(actionRenders);
            }
        }

        [Theory]
        [InlineData(true)]
        [InlineData(false)]
        public void SwapForSameTip(bool render)
        {
            BlockChain<DumbAction> fork = _blockChain.Fork(_blockChain.Tip.Hash);
            IReadOnlyList<RenderRecord<DumbAction>> prevRecords = _renderer.Records;
            _blockChain.Swap(fork, render: render);

            // Render methods should be invoked if and only if the tip changes
            Assert.Equal(prevRecords, _renderer.Records);
        }

        [Theory]
        [InlineData(true)]
        [InlineData(false)]
        public async Task SwapWithoutReorg(bool render)
        {
            BlockChain<DumbAction> fork = _blockChain.Fork(_blockChain.Tip.Hash);

            // The lower  chain goes to the higher chain  [#N -> #N+1]
            await fork.MineBlock(default);
            IReadOnlyList<RenderRecord<DumbAction>.Reorg> prevRecords = _renderer.ReorgRecords;
            _blockChain.Swap(fork, render: render);

            // RenderReorg() should be invoked if and only if the actual reorg happens
            Assert.Equal(prevRecords, _renderer.ReorgRecords);
        }

        [Fact]
        public async Task TreatGoingBackwardAsReorg()
        {
            BlockChain<DumbAction> fork = _blockChain.Fork(_blockChain.Tip.Hash);

            // The higher chain goes to the lower  chain  [#N -> #N-1]
            await _blockChain.MineBlock(default);
            IReadOnlyList<RenderRecord<DumbAction>.Reorg> prevRecords = _renderer.ReorgRecords;
            _blockChain.Swap(fork, render: true);

            // RenderReorg() should be invoked if and only if the actual reorg happens
            Assert.Equal(prevRecords.Count + 2, _renderer.ReorgRecords.Count);
            Assert.Equal(prevRecords, _renderer.ReorgRecords.Take(prevRecords.Count));
            RenderRecord<DumbAction>.Reorg begin = _renderer.ReorgRecords[prevRecords.Count];
            Assert.True(begin.Begin);
            RenderRecord<DumbAction>.Reorg end = _renderer.ReorgRecords[prevRecords.Count + 1];
            Assert.True(end.End);
        }

        [Theory]
        [InlineData(true)]
        [InlineData(false)]
        public async Task ReorgIsUnableToHeterogenousChain(bool render)
        {
            using (var fx2 = new DefaultStoreFixture(
                memory: true, blockAction: _policy.BlockAction))
            {
                Block<DumbAction> genesis2 = TestUtils.MineGenesis<DumbAction>(
                    _policy.GetHashAlgorithm,
                    timestamp: DateTimeOffset.UtcNow
                ).AttachStateRootHash(fx2.StateStore, _policy);
                var chain2 = new BlockChain<DumbAction>(
                    _policy,
                    _stagePolicy,
                    fx2.Store,
                    fx2.StateStore,
                    genesis2
                );
                for (int i = 0; i < 5; i++)
                {
                    await _blockChain.MineBlock(default);
                    await chain2.MineBlock(default);
                }

                Log.Logger.CompareBothChains(
                    LogEventLevel.Debug,
                    nameof(_blockChain),
                    _blockChain,
                    nameof(chain2),
                    chain2
                );

                Assert.Throws<InvalidGenesisBlockException>(() =>
                    _blockChain.Swap(chain2, render)
                );
            }
        }

        // This is a regression test for:
        // https://github.com/planetarium/libplanet/issues/189#issuecomment-482443607.
        [Fact]
        public void GetStateOnlyDrillsDownUntilRequestedAddressesAreFound()
        {
            var policy = new NullPolicy<DumbAction>();
            var tracker = new StoreTracker(_fx.Store);
            var chain = new BlockChain<DumbAction>(
                policy,
                new VolatileStagePolicy<DumbAction>(),
                tracker,
                _fx.StateStore,
                _fx.GenesisBlock
            );

            Block<DumbAction> b = chain.Genesis;
            Address[] addresses = new Address[30];
            for (int i = 0; i < addresses.Length; ++i)
            {
                var privateKey = new PrivateKey();
                Address address = privateKey.ToAddress();
                addresses[i] = address;
                DumbAction[] actions =
                {
                    new DumbAction(address, "foo"),
                    new DumbAction(i < 1 ? address : addresses[i - 1], "bar"),
                };
                Transaction<DumbAction>[] txs =
                {
                    Transaction<DumbAction>.Create(0, privateKey, chain.Genesis.Hash, actions),
                };
                b = TestUtils.MineNext(
                    b,
                    policy.GetHashAlgorithm,
                    txs
                ).AttachStateRootHash(_fx.StateStore, policy);
                chain.Append(b);
            }

            tracker.ClearLogs();
            int testingDepth = addresses.Length / 2;
            Address[] targetAddresses = Enumerable.Range(
                testingDepth,
                Math.Min(10, addresses.Length - testingDepth - 1)
            ).Select(i => addresses[i]).ToArray();

            foreach (Address targetAddress in targetAddresses)
            {
                Assert.NotNull(chain.GetState(targetAddress));
            }

            var callCount = tracker.Logs.Where(
                trackLog => trackLog.Method == "GetBlockStates"
            ).Select(trackLog => trackLog.Params).Count();
            Assert.True(testingDepth >= callCount);
        }

        [Fact]
        public void GetStateReturnsEarlyForNonexistentAccount()
        {
            var blockPolicy = new NullPolicy<DumbAction>();
            var tracker = new StoreTracker(_fx.Store);
            var chain = new BlockChain<DumbAction>(
                blockPolicy,
                new VolatileStagePolicy<DumbAction>(),
                tracker,
                _fx.StateStore,
                _fx.GenesisBlock
            );

            Block<DumbAction> b = chain.Genesis;
            for (int i = 0; i < 20; ++i)
            {
                b = TestUtils.MineNext(
                    b,
                    blockPolicy.GetHashAlgorithm,
                    blockInterval: TimeSpan.FromSeconds(10)
                ).AttachStateRootHash(_fx.StateStore, blockPolicy);
                chain.Append(b);
            }

            tracker.ClearLogs();
            Address nonexistent = new PrivateKey().ToAddress();
            IValue result = chain.GetState(nonexistent);
            Assert.Null(result);
            var callCount = tracker.Logs.Where(
                trackLog => trackLog.Method == "GetBlockStates"
            ).Select(trackLog => trackLog.Params).Count();
            Assert.True(
                callCount <= 1,
                $"GetBlocksStates() was called {callCount} times"
            );
        }

        [Fact]
        public async void GetStateReturnsValidStateAfterFork()
        {
            HashAlgorithmType hashAlgorithm = HashAlgorithmType.Of<SHA256>();
            Block<DumbAction> genesisBlock = BlockChain<DumbAction>.MakeGenesisBlock(
                hashAlgorithm,
                new[] { new DumbAction(_fx.Address1, "item0.0", idempotent: true) }
            );
            var privateKey = new PrivateKey();
            var store = new DefaultStore(path: null);
            var stateStore =
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore());

            var chain =
                new BlockChain<DumbAction>(
                    new NullPolicy<DumbAction>(),
                    new VolatileStagePolicy<DumbAction>(),
                    store,
                    stateStore,
                    genesisBlock);
            Assert.Equal("item0.0", (Text)chain.GetState(_fx.Address1));

            chain.MakeTransaction(
                privateKey,
                new[] { new DumbAction(_fx.Address1, "item1.0"), }
            );
            await chain.MineBlock(_fx.Address1);
            Assert.Equal("item0.0,item1.0", (Text)chain.GetState(_fx.Address1));

            var forked = chain.Fork(chain.Tip.Hash);
            Assert.Equal(2, forked.Count);
            Assert.Equal("item0.0,item1.0", (Text)forked.GetState(_fx.Address1));
        }

        [Fact]
        public void GetStateWithStateCompleter()
        {
            (Address signer, Address[] addresses, BlockChain<DumbAction> chain)
                = MakeIncompleteBlockStates();
            StoreTracker store = (StoreTracker)chain.Store;

            IValue value = chain.GetState(
                addresses[4],
                chain.BlockHashes.Skip(addresses.Length).First(),
                (bc, hash, addr) =>
                {
                    bc.RecalculateBlockStates(hash);
                    return new Text($"{bc.Id}/{hash}/{addr}: callback called");
                }
            );
            BlockHash prevUpdate = chain.BlockHashes.Skip(addresses.Length).First();
            var expected = new Text($"{chain.Id}/{prevUpdate}/{addresses[4]}: callback called");
            Assert.Equal(expected, value);
        }

        [Fact]
        public async void GetStateReturnsLatestStatesWhenMultipleAddresses()
        {
            var privateKeys = Enumerable.Range(1, 10).Select(_ => new PrivateKey()).ToList();
            var addresses = privateKeys.Select(AddressExtensions.ToAddress).ToList();
            var chain = new BlockChain<DumbAction>(
                new NullPolicy<DumbAction>(),
                new VolatileStagePolicy<DumbAction>(),
                _fx.Store,
                _fx.StateStore,
                _fx.GenesisBlock);

            foreach (var address in addresses)
            {
                Assert.Null(chain.GetState(address));
            }

            var privateKeysAndAddresses10 = privateKeys.Zip(addresses, (k, a) => (k, a));
            foreach (var (key, address) in privateKeysAndAddresses10)
            {
                chain.MakeTransaction(key, new[] { new DumbAction(address, "1") });
            }

            await chain.MineBlock(addresses[0]);

            foreach (var address in addresses)
            {
                Assert.Equal((Text)"1", chain.GetState(address));
            }

            chain.MakeTransaction(privateKeys[0], new[] { new DumbAction(addresses[0], "2") });
            await chain.MineBlock(addresses[0]);
            Assert.Equal((Text)"1,2", chain.GetState(addresses[0]));
        }

        [Fact]
        public async void FindBranchPoint()
        {
            HashAlgorithmType hashAlgorithm = HashAlgorithmType.Of<SHA256>();
            Block<DumbAction> b1 = await _blockChain.MineBlock(_fx.Address1);
            Block<DumbAction> b2 = await _blockChain.MineBlock(_fx.Address1);
            Block<DumbAction> b3 = await _blockChain.MineBlock(_fx.Address1);
            Block<DumbAction> b4 = await _blockChain.MineBlock(_fx.Address1);

            Assert.Equal(b1.PreviousHash, _blockChain.Genesis.Hash);

            var emptyLocator = new BlockLocator(new BlockHash[0]);
            var locator = new BlockLocator(new[] { b4.Hash, b3.Hash, b1.Hash });

            using (var emptyFx = new DefaultStoreFixture(
                memory: true, blockAction: _policy.BlockAction))
            using (var forkFx = new DefaultStoreFixture(
                memory: true, blockAction: _policy.BlockAction))
            {
                var genesisBlock = BlockChain<DumbAction>.MakeGenesisBlock(hashAlgorithm);
                var emptyChain = new BlockChain<DumbAction>(
                    _blockChain.Policy,
                    new VolatileStagePolicy<DumbAction>(),
                    emptyFx.Store,
                    emptyFx.StateStore,
                    emptyFx.GenesisBlock);
                var fork = new BlockChain<DumbAction>(
                    _blockChain.Policy,
                    new VolatileStagePolicy<DumbAction>(),
                    forkFx.Store,
                    forkFx.StateStore,
                    forkFx.GenesisBlock);
                fork.Append(b1);
                fork.Append(b2);
                await fork.MineBlock(_fx.Address1);

                Assert.Null(emptyChain.FindBranchpoint(emptyLocator));
                Assert.Null(emptyChain.FindBranchpoint(locator));

                Assert.Null(_blockChain.FindBranchpoint(emptyLocator));
                Assert.Equal(b4.Hash, _blockChain.FindBranchpoint(locator));

                Assert.Null(fork.FindBranchpoint(emptyLocator));
                Assert.Equal(b1.Hash, fork.FindBranchpoint(locator));
            }
        }

        [Fact]
        public void GetNextTxNonce()
        {
            var privateKey = new PrivateKey();
            Address address = privateKey.ToAddress();
            var actions = new[] { new DumbAction(_fx.Address1, "foo") };
            var genesis = _blockChain.Genesis;

            Assert.Equal(0, _blockChain.GetNextTxNonce(address));

            Transaction<DumbAction>[] txsA =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 0),
            };

            Block<DumbAction> b1 = TestUtils.MineNext(
                genesis,
                _policy.GetHashAlgorithm,
                txsA,
                null,
                _policy.GetNextBlockDifficulty(_blockChain),
                blockInterval: TimeSpan.FromSeconds(10)
            ).AttachStateRootHash(_fx.StateStore, _policy);
            _blockChain.Append(b1);

            Assert.Equal(1, _blockChain.GetNextTxNonce(address));

            Transaction<DumbAction>[] txsB =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 1),
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 2),
            };

            StageTransactions(txsB);

            Assert.Equal(3, _blockChain.GetNextTxNonce(address));

            Transaction<DumbAction>[] txsC =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 3),
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 3),
            };
            StageTransactions(txsC);

            Assert.Equal(4, _blockChain.GetNextTxNonce(address));

            Transaction<DumbAction>[] txsD =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 5),
            };
            StageTransactions(txsD);

            Assert.Equal(4, _blockChain.GetNextTxNonce(address));

            Transaction<DumbAction>[] txsE =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 4),
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 5),
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 7),
            };
            StageTransactions(txsE);

            foreach (var tx in _blockChain.StagePolicy.Iterate(_blockChain))
            {
                _logger.Fatal(
                    "{Id}; {Signer}; {Nonce}; {Timestamp}",
                    tx.Id,
                    tx.Signer,
                    tx.Nonce,
                    tx.Timestamp);
            }

            Assert.Equal(6, _blockChain.GetNextTxNonce(address));
        }

        [Fact]
        public async Task GetNextTxNonceWithStaleTx()
        {
            var privateKey = new PrivateKey();
            var address = privateKey.ToAddress();
            var actions = new[] { new DumbAction(address, "foo") };

            Transaction<DumbAction>[] txs =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey),
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 1),
            };

            StageTransactions(txs);
            await _blockChain.MineBlock(address);

            Transaction<DumbAction>[] staleTxs =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 0),
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 1),
            };
            StageTransactions(staleTxs);

            Assert.Equal(2, _blockChain.GetNextTxNonce(address));

            _blockChain.MakeTransaction(privateKey, actions);
            Assert.Equal(3, _blockChain.GetNextTxNonce(address));

            _blockChain.MakeTransaction(privateKey, actions);
            Assert.Equal(4, _blockChain.GetNextTxNonce(address));
        }

        [Fact]
        public void ValidateTxNonces()
        {
            var privateKey = new PrivateKey();
            var actions = new[] { new DumbAction(_fx.Address1, string.Empty) };

            var genesis = _blockChain.Genesis;

            Block<DumbAction> MineNext(
                Block<DumbAction> block,
                IReadOnlyList<Transaction<DumbAction>> txs
            ) =>
                TestUtils.MineNext(
                    block,
                    _policy.GetHashAlgorithm,
                    txs,
                    difficulty: 1024,
                    blockInterval: TimeSpan.FromSeconds(10)
                ).AttachStateRootHash(_fx.StateStore, _policy);

            Transaction<DumbAction>[] txsA =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 1),
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 0),
            };
            Block<DumbAction> b1 = MineNext(genesis, txsA);
            _blockChain.Append(b1);

            Transaction<DumbAction>[] txsB =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 2),
            };
            Block<DumbAction> b2 = MineNext(b1, txsB);
            _blockChain.Append(b2);

            // Invalid if nonce is too low
            Transaction<DumbAction>[] txsC =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 1),
            };
            Block<DumbAction> b3a = MineNext(b2, txsC);
            Assert.Throws<InvalidTxNonceException>(() => _blockChain.Append(b3a));

            // Invalid if nonce is too high
            Transaction<DumbAction>[] txsD =
            {
                _fx.MakeTransaction(actions, privateKey: privateKey, nonce: 4),
            };
            Block<DumbAction> b3b = MineNext(b2, txsD);
            Assert.Throws<InvalidTxNonceException>(() => _blockChain.Append(b3b));
        }

        [Fact]
        public void MakeTransaction()
        {
            var privateKey = new PrivateKey();
            Address address = privateKey.ToAddress();
            var actions = new[] { new DumbAction(address, "foo") };

            _blockChain.MakeTransaction(privateKey, actions);
            _blockChain.MakeTransaction(privateKey, actions);

            List<Transaction<DumbAction>> txs = _stagePolicy
                .Iterate(_blockChain)
                .OrderBy(tx => tx.Nonce)
                .ToList();

            Assert.Equal(2, txs.Count);

            var transaction = txs[0];
            Assert.Equal(0, transaction.Nonce);
            Assert.Equal(address, transaction.Signer);
            Assert.Equal(actions, transaction.Actions);

            transaction = txs[1];
            Assert.Equal(1, transaction.Nonce);
            Assert.Equal(address, transaction.Signer);
            Assert.Equal(actions, transaction.Actions);
        }

        [Fact]
        public async Task MakeTransactionConcurrency()
        {
            var privateKey = new PrivateKey();
            Address address = privateKey.ToAddress();
            var actions = new[] { new DumbAction(address, "foo") };

            var tasks = Enumerable.Range(0, 10)
                .Select(_ => Task.Run(() => _blockChain.MakeTransaction(privateKey, actions)));

            await Task.WhenAll(tasks);

            var txIds = _blockChain.GetStagedTransactionIds();

            var nonces = txIds
                .Select(id => _stagePolicy.Get(_blockChain, id, includeUnstaged: true)
                    ?? _blockChain.GetTransaction(id))
                .Select(tx => tx.Nonce)
                .OrderBy(nonce => nonce)
                .ToArray();

            Assert.Equal(
                nonces,
                new long[] { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 }
            );
        }

        [Fact]
        public async void BlockActionWithMultipleAddress()
        {
            var miner0 = _blockChain.Genesis.Miner;
            var miner1 = _fx.Address1;
            var miner2 = _fx.Address2;
            var rewardRecordAddress = MinerReward.RewardRecordAddress;

            await _blockChain.MineBlock(miner1);
            await _blockChain.MineBlock(miner1);
            await _blockChain.MineBlock(miner2);

            IValue miner1state = _blockChain.GetState(miner1);
            IValue miner2state = _blockChain.GetState(miner2);
            IValue rewardState = _blockChain.GetState(rewardRecordAddress);

            int reward1 = (Integer)miner1state;
            int reward2 = (Integer)miner2state;

            Assert.Equal(2, reward1);
            Assert.Equal(1, reward2);

            Assert.Equal((Text)$"{miner0},{miner1},{miner1},{miner2}", rewardState);
        }

        /// <summary>
        /// Builds a fixture that has incomplete states for blocks other
        /// than the tip, to test <c>GetState()</c> method's
        /// <c>completeStates: true</c> option and
        /// <see cref="IncompleteBlockStatesException"/>.
        ///
        /// <para>The fixture this makes has total 5 addresses (i.e., accounts;
        /// these go to the second item of the returned triple) and 11 blocks
        /// (these go to the third item of the returned triple). Every block
        /// contains a transaction within an action that mutates one account
        /// state except for the genesis block.  All transactions in the fixture
        /// are signed by one private key (its address goes to the first item
        /// of the returned triple).  The most important thing is that
        /// these blocks all lack its states except for the last block (tip).
        /// Overall blocks in the fixture look like:</para>
        ///
        /// <code>
        ///  Index   UpdatedAddresses   States in Store
        /// ------- ------------------ -----------------
        ///      0                      Absent
        ///      1   addresses[0]       Absent
        ///      2   addresses[1]       Absent
        ///      3   addresses[2]       Absent
        ///      4   addresses[3]       Absent
        ///      5   addresses[4]       Absent
        ///      6   addresses[0]       Absent
        ///      7   addresses[1]       Absent
        ///      8   addresses[2]       Absent
        ///      9   addresses[3]       Absent
        ///     10   addresses[4]       Present
        /// </code>
        /// </summary>
        internal static (Address, Address[] Addresses, BlockChain<DumbAction> Chain)
            MakeIncompleteBlockStates(
                IStore store,
                IStateStore stateStore,
                IRenderer<DumbAction> renderer = null
            )
        {
            IBlockPolicy<DumbAction> blockPolicy = new NullPolicy<DumbAction>();
            store = new StoreTracker(store);
            Guid chainId = Guid.NewGuid();
            Block<DumbAction> genesisBlock = TestUtils.MineGenesis<DumbAction>(
                blockPolicy.GetHashAlgorithm
            ).AttachStateRootHash(stateStore, blockPolicy);
            var chain = new BlockChain<DumbAction>(
                blockPolicy,
                new VolatileStagePolicy<DumbAction>(),
                store,
                stateStore,
                chainId,
                genesisBlock,
                renderers: renderer is null ? null : new[] { renderer }
            );
            var privateKey = new PrivateKey();
            Address signer = privateKey.ToAddress();

            void BuildIndex(Guid id, Block<DumbAction> block)
            {
                foreach (Transaction<DumbAction> tx in block.Transactions)
                {
                    store.IncreaseTxNonce(id, tx.Signer);
                }

                store.AppendIndex(id, block.Hash);
            }

            // Build a store with incomplete states
            Block<DumbAction> b = chain.Genesis;
            AccountStateGetter nullAccountStateGetter = (address) => null;
            AccountBalanceGetter nullAccountBalanceGetter =
                (address, currency) => new FungibleAssetValue(currency);
            IAccountStateDelta previousStates = b.ProtocolVersion > 0
                ? new AccountStateDeltaImpl(
                    nullAccountStateGetter,
                    nullAccountBalanceGetter,
                    b.Miner)
                : new AccountStateDeltaImplV0(
                    nullAccountStateGetter,
                    nullAccountBalanceGetter,
                    b.Miner);
            ActionEvaluation[] evals = chain.ActionEvaluator.EvaluateBlock(
                b,
                DateTimeOffset.UtcNow,
                previousStates).ToArray();
            IImmutableDictionary<Address, IValue> dirty = evals.GetDirtyStates();
            IImmutableDictionary<(Address, Currency), FungibleAssetValue> balances =
                evals.GetDirtyBalances();
            const int accountsCount = 5;
            Address[] addresses = Enumerable.Repeat<object>(null, accountsCount)
                .Select(_ => new PrivateKey().ToAddress())
                .ToArray();
            for (int i = 0; i < 2; ++i)
            {
                for (int j = 0; j < accountsCount; ++j)
                {
                    int index = i * accountsCount + j;
                    Transaction<DumbAction> tx = Transaction<DumbAction>.Create(
                        store.GetTxNonce(chainId, signer),
                        privateKey,
                        chain.Genesis.Hash,
                        new[] { new DumbAction(addresses[j], index.ToString()) }
                    );
                    b = TestUtils.MineNext(
                        b,
                        blockPolicy.GetHashAlgorithm,
                        new[] { tx },
                        blockInterval: TimeSpan.FromSeconds(10)
                    ).AttachStateRootHash(stateStore, blockPolicy);
                    previousStates = b.ProtocolVersion > 0
                        ? new AccountStateDeltaImpl(
                            dirty.GetValueOrDefault,
                            (address, currency) => balances.GetValueOrDefault((address, currency)),
                            b.Miner)
                        : new AccountStateDeltaImplV0(
                            dirty.GetValueOrDefault,
                            (address, currency) => balances.GetValueOrDefault((address, currency)),
                            b.Miner);

                    dirty = chain.ActionEvaluator.EvaluateBlock(
                        b,
                        DateTimeOffset.UtcNow,
                        previousStates).GetDirtyStates();
                    Assert.NotEmpty(dirty);
                    store.PutBlock(b);
                    BuildIndex(chainId, b);
                    Assert.Equal(b, chain[b.Hash]);
                }
            }

            if (stateStore is TrieStateStore trieStateStore)
            {
                trieStateStore.PruneStates(ImmutableHashSet<BlockHash>.Empty.Add(b.Hash));
            }

            return (signer, addresses, chain);
        }

        private (Address, Address[] Addresses, BlockChain<DumbAction> Chain)
            MakeIncompleteBlockStates() =>
            MakeIncompleteBlockStates(_fx.Store, _fx.StateStore);

        private (Address[], Transaction<DumbAction>[]) MakeFixturesForAppendTests(
            PrivateKey privateKey = null,
            DateTimeOffset epoch = default
        )
        {
            Address[] addresses =
            {
                _fx.Address1,
                _fx.Address2,
                _fx.Address3,
                _fx.Address4,
                _fx.Address5,
            };

            privateKey = privateKey ?? new PrivateKey(new byte[]
            {
                0xa8, 0x21, 0xc7, 0xc2, 0x08, 0xa9, 0x1e, 0x53, 0xbb, 0xb2,
                0x71, 0x15, 0xf4, 0x23, 0x5d, 0x82, 0x33, 0x44, 0xd1, 0x16,
                0x82, 0x04, 0x13, 0xb6, 0x30, 0xe7, 0x96, 0x4f, 0x22, 0xe0,
                0xec, 0xe0,
            });

            Transaction<DumbAction>[] txs =
            {
                _fx.MakeTransaction(
                    new[]
                    {
                        new DumbAction(addresses[0], "foo"),
                        new DumbAction(addresses[1], "bar"),
                    },
                    timestamp: epoch,
                    nonce: 0,
                    privateKey: privateKey),
                _fx.MakeTransaction(
                    new[]
                    {
                        new DumbAction(addresses[2], "baz"),
                        new DumbAction(addresses[3], "qux"),
                    },
                    timestamp: epoch.AddSeconds(5),
                    nonce: 1,
                    privateKey: privateKey),
            };

            return (addresses, txs);
        }

        [Fact]
        private async void TipChanged()
        {
            var genesis = _blockChain.Genesis;

            _renderer.ResetRecords();

            // Mine block
            Assert.Empty(_renderer.BlockRecords);
            Block<DumbAction> block = await _blockChain.MineBlock(_fx.Address1);
            IReadOnlyList<RenderRecord<DumbAction>.Block> records = _renderer.BlockRecords;
            Assert.Equal(2, records.Count);
            foreach (RenderRecord<DumbAction>.Block record in records)
            {
                Assert.Equal(genesis, record.OldTip);
                Assert.Equal(block, record.NewTip);
                Assert.Equal(1, record.NewTip.Index);
            }

            _renderer.ResetRecords();
            Assert.Throws<InvalidBlockIndexException>(() => _blockChain.Append(block));
            Assert.Empty(_renderer.BlockRecords);

            // TODO: Add test cases for swap
        }

        [Fact]
        private async void Reorged()
        {
            _renderer.ResetRecords();
            var branchpoint = _blockChain.Tip;
            var fork = _blockChain.Fork(_blockChain.Tip.Hash);
            await fork.MineBlock(_fx.Address1);
            await fork.MineBlock(_fx.Address2);
            await _blockChain.MineBlock(_fx.Address3);

            var oldTip = _blockChain.Tip;
            var newTip = fork.Tip;

            Assert.Empty(_renderer.ReorgRecords);

            _blockChain.Swap(fork, true);

            IReadOnlyList<RenderRecord<DumbAction>.Reorg> reorgRecords = _renderer.ReorgRecords;
            Assert.Equal(2, reorgRecords.Count);
            foreach (RenderRecord<DumbAction>.Reorg reorgRecord in reorgRecords)
            {
                Assert.Equal(oldTip, reorgRecord.OldTip);
                Assert.Equal(newTip, reorgRecord.NewTip);
                Assert.Equal(branchpoint, reorgRecord.Branchpoint);
            }
        }

        [Fact]
        private void ConstructWithGenesisBlock()
        {
            var storeFixture = new DefaultStoreFixture();
            var policy = new NullPolicy<DumbAction>();

            var addresses = ImmutableList<Address>.Empty
                .Add(storeFixture.Address1)
                .Add(storeFixture.Address2)
                .Add(storeFixture.Address3);

            var actions =
                addresses
                    .Select((address, index) => new DumbAction(address, index.ToString()))
                    .ToArray();
            HashAlgorithmType hashAlgorithm = policy.GetHashAlgorithm(0);
            BlockChain<DumbAction> blockChain =
                new BlockChain<DumbAction>(
                    policy,
                    new VolatileStagePolicy<DumbAction>(),
                    storeFixture.Store,
                    storeFixture.StateStore,
                    BlockChain<DumbAction>.MakeGenesisBlock(hashAlgorithm, actions));

            Assert.Equal(addresses, blockChain.Genesis.Transactions.First().UpdatedAddresses);

            var states = addresses.Select(address => blockChain.GetState(address))
                .ToArray();
            for (int i = 0; i < states.Length; ++i)
            {
                Assert.Equal((Text)states[i], i.ToString());
            }
        }

        [Fact]
        private void ConstructWithUnexpectedGenesisBlock()
        {
            var policy = new NullPolicy<DumbAction>();
            HashAlgorithmType hashAlgorithm = policy.GetHashAlgorithm(0);
            var stagePolicy = new VolatileStagePolicy<DumbAction>();
            var store = new DefaultStore(null);
            var stateStore =
                new TrieStateStore(new MemoryKeyValueStore(), new MemoryKeyValueStore());
            var genesisBlockA = BlockChain<DumbAction>.MakeGenesisBlock(hashAlgorithm);
            var genesisBlockB = BlockChain<DumbAction>.MakeGenesisBlock(hashAlgorithm);

            var blockChain = new BlockChain<DumbAction>(
                policy,
                stagePolicy,
                store,
                stateStore,
                genesisBlockA
            );

            Assert.Throws<InvalidGenesisBlockException>(() =>
            {
                var blockchain = new BlockChain<DumbAction>(
                    policy,
                    stagePolicy,
                    store,
                    stateStore,
                    genesisBlockB
                );
            });
        }

        [Fact]
        private async Task IgnoreLowerNonceTxWhenStaging()
        {
            var privateKey = new PrivateKey();
            var address = privateKey.ToAddress();
            var txsA = Enumerable.Range(0, 3)
                .Select(nonce => _fx.MakeTransaction(
                    nonce: nonce, privateKey: privateKey, timestamp: DateTimeOffset.Now))
                .ToArray();
            StageTransactions(txsA);
            Block<DumbAction> b1 = await _blockChain.MineBlock(address);
            Assert.Equal(txsA, b1.Transactions);

            var txsB = Enumerable.Range(0, 4)
                .Select(nonce => _fx.MakeTransaction(
                    nonce: nonce, privateKey: privateKey, timestamp: DateTimeOffset.Now))
                .ToArray();
            StageTransactions(txsB);

            // Stage only txs having higher or equal with nonce than expected nonce.
            Assert.Single(_blockChain.GetStagedTransactionIds());
        }

        [Fact]
        private void ConstructBlockchainWithGenesisBlockHavingStateRootHash()
        {
            var store = new DefaultStore(null);
            var stateStore = new TrieStateStore(
                new MemoryKeyValueStore(), new MemoryKeyValueStore());
            Block<DumbAction> genesisBlock =
                TestUtils.MineGenesis<DumbAction>(_policy.GetHashAlgorithm);
            BlockChain<DumbAction> blockChain = TestUtils.MakeBlockChain(
                _policy, store, stateStore, genesisBlock: genesisBlock);

            Assert.NotNull(blockChain[0].StateRootHash);
        }
    }
}
