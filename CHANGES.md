Libplanet changelog
===================

Version 0.12.0
--------------

To be released.

### Backward-incompatible API changes

 -  Block hashes are now represented as `BlockHash`, which was introduced in
    this release, which has been done as `HashDigest<SHA256>`.
    [[#1192], [#1197]]
     -  Removed `HashDigest<T>.Satisfies()` method.  This was replaced by
        `BlockHash.Satisfies()` method instead.
     -  The type of `Block<T>.Hash` property became `BlockHash`
        (was `HashDigest<SHA256>`).
     -  The type of `Block<T>.PreviousHash` property became `BlockHash?`
        (was `HashDigest<SHA256>?`).
     -  The type of `Block<T>.PreEvaluationHash` property became `BlockHash?`
        (was `HashDigest<SHA256>?`).
     -  The types of `Block<T>()` constructors' `hash` parameter became
        `BlockHash` (were `HashDigest<SHA256>`).
     -  The types of `Block<T>()` constructors' `previousHash` parameter became
        `BlockHash?` (were `HashDigest<SHA256>?`).
     -  The types of `Block<T>()` constructors' `preEvaluationHash` parameter
        became `BlockHash?` (were `HashDigest<SHA256>?`).
     -  The type of `Block<T>.Mine()` method's `previousHash` parameter became
        `BlockHash?` (was `HashDigest<SHA256>?`).
     -  The return type of `HashCash.Hash()` method became `BlockHash`
        (was `HashDigest<SHA256>`).
     -  The type of `Transaction<T>()` constructor's `genesisHash` parameter
        became `BlockHash?` (was `HashDigest<SHA256>?`).
     -  The type of `Transaction<T>.Create()` method's `genesisHash` parameter
        became `BlockHash?` (was `HashDigest<SHA256>?`).
     -  The type of `Transaction<T>.GenesisHash` property became `BlockHash?`
        (was `HashDigest<SHA256>?`).
     -  The type of `Transaction<T>.EvaluateActionsGradually()` method's
        `blockHash` parameter became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `Transaction<T>.EvaluateActions()` method's `blockHash`
        parameter became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `BlockChain[]` indexer's parameter became `BlockHash`
        (was `HashDigest<SHA256>`).
     -  The type of `BlockChain.BlockHashes` property became
        `IEnumerable<BlockHash>` (was `IEnumerable<HashDigest<SHA256>>`).
     -  The type of `BlockChain.ContainsBlock()` method's `blockHash` parameter
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `BlockChain.GetState()` method's `offset` parameter
        became `BlockHash?` (was `HashDigest<SHA256>?`).
     -  The type of `BlockChain.GetBalance()` method's `offset` parameter
        became `BlockHash?` (was `HashDigest<SHA256>?`).
     -  The type of `StateCompleter<T>` delegate's `blockHash` parameter
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `FungibleAssetStateCompleter<T>` delegate's `blockHash`
        parameter became `BlockHash` (was `HashDigest<SHA256>`).
     -  `BlockSet<T>` no more implements
        `IDictionary<HashDigest<SHA256>, Block<T>>`, but now implements
        `IDictionary<BlockHash, Block<T>>`.
     -  The type of `ActionExecutionState.ExecutedBlockHash` property became
        `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `BlockDownloadState.ReceivedBlockHash` property became
        `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `BlockVerificationState.VerifiedBlockHash` property became
        `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `ActionEvaluation.EvaluateActionsGradually()` method's
        `blockHash` parameter became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `UnexpectedlyTerminatedActionException()` constructor's
        `blockHash` parameter became `BlockHash?` (was `HashDigest<SHA256>?`).
     -  The type of `UnexpectedlyTerminatedActionException.BlockHash` property
        became `BlockHash?` (was `HashDigest<SHA256>?`).
     -  The type of `IncompleteBlockStatesException()` constructor's
        `blockHash` parameter became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `IncompleteBlockStatesException.BlockHash` property
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The types of `InvalidGenesisBlockException()` constructor's
        `networkExpected` and `stored` parameters became `BlockHash`
        (were `HashDigest<SHA256>`).
     -  The type of `InvalidGenesisBlockException.NetworkExpected` property
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `InvalidGenesisBlockException.Stored` property
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `InvalidTxGenesisHashException()` constructor's
        `expectedGenesisHash` parameter became `BlockHash`
        (was `HashDigest<SHA256>`).
     -  The type of `InvalidTxGenesisHashException()` constructor's
        `improperGenesisHash` parameter became `BlockHash?`
        (was `HashDigest<SHA256>?`).
     -  The type of `InvalidTxGenesisHashException.ExpectedGenesisHash` property
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `InvalidTxGenesisHashException.ImproperGenesisHash` property
        became `BlockHash?` (was `HashDigest<SHA256>?`).
     -  The return type of `IStore.IndexBlockHash()` method became `BlockHash?`
        (was `HashDigest<SHA256>?`).
     -  The type of `IStore.AppendIndex()` method's `hash` parameter became
        `BlockHash` (was `HashDigest<SHA256>`).
     -  Replaced `IStore.ForkBlockIndexes()` method's
        `HashDigest<SHA256> branchPoint` parameter with `BlockHash branchpoint`.
     -  The return type of `IStore.IterateIndexes()` method became
        `IEnumerable<BlockHash>` (was `IEnumerable<HashDigest<SHA256>>`).
     -  The return type of `IStore.IterateBlockHashes()` method became
        `IEnumerable<BlockHash>` (was `IEnumerable<HashDigest<SHA256>>`).
     -  The type of `IStore.GetBlock<T>()` method's `blockHash` parameter
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `IStore.GetBlockIndex()` method's `blockHash` parameter
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `IStore.GetBlockDigest()` method's `blockHash` parameter
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `IStore.DeleteBlock()` method's `blockHash` parameter
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `IStore.ContainsBlock()` method's `blockHash` parameter
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `IStateStore.GetState()` method's `blockHash` parameter
        became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `IStateStore.ContainsBlockStates()` method's `blockHash`
        parameter became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `TrieStateStore.GetRootHash()` method's `blockHash`
        parameter became `BlockHash` (was `HashDigest<SHA256>`).
     -  The type of `TrieStateStore.PruneStates()` method's `excludeBlockHashes`
        parameter became `IImmutableSet<BlockHash>`
        (was `ImmutableHashSet<HashDigest<SHA256>>`).
 -  Added `IActionContext.TxId` property.  [[#1275]]
 -  Added `IStore.PutTxExecution(TxSuccess)` method.  [[#1156], [#1289]]
 -  Added `IStore.PutTxExecution(TxFailure)` method.  [[#1156], [#1289]]
 -  Added `IStore.GetTxExecution()` method.  [[#1156], [#1289]]
 -  Removed the optional parameter `Guid? chainId = null` from
    `IStateStore.GetState()` method.  [[#1289]]
 -  Removed `compress` parameter from `DefaultStore()` constructor.  [[#1289]]
 -  Removed `statesCacheSize` parameter from `DefaultStore()` constructor.
    [[#1289]]
 -  Removed `StunMessage.Parse(Stream)` method.  [[#1228]]
 -  Moved `ITransport` and `NetMQTransport` from `Libplanet.Net` to
    `Libplanet.Net.Transports`.  [[#1235]]
 -  `Block<T>` now enforces a collection of `Transaction<T>`s to be less
    mutable.  [[#1274]]
     -  The type of `Block<T>()` constructor's `transactions` parameter became
        `IReadOnlyList<T>` (was `IEnumerable<T>`).
     -  The type of `Transactions` property of `Block<T>` became
        `IReadOnlyList<T>` (was `IEnumerable<T>`).
 -  Types of following properties became `IReadOnlyList<T>`
    (was `IEnumerable<T>`).  [[#1230], [#1271]]
     -  `RoutingTable.Peers`
     -  `RoutingTable.PeerStates`
     -  `Swarm<T>.Peers`
     -  `Swarm<T>.PeerStates`
 -  Return type of `RoutingTable.Neighbors()` became `IReadOnlyList<BoundPeer>`
    (was `IEnumerable<BoundPeer>`).  [[#1230], [#1271]]
 -  All methods pertaining to evaluating `IAction`s are moved
    to a new `ActionEvaluator` class.  [[#1301], [#1305]]
     -  Removed `Block<T>.Evaluate()` method.
        Use `ActionEvaluator.Evaluate()` method instead.
     -  Removed `Block<T>.EvaluateActionsPerTx()` method.
     -  Removed `Transaction<T>.EvaluateActionsGradually()` method.
     -  Removed `Transaction<T>.EvaluateActions()` method.
 -  Parameters `action`, `inputContext`, and `outputStates` for
    `ActionEvaluation()` constructor can no longer be `null`.  [[#1305]]
 -  Added `IStore.PutTxIdBlockHashIndex(TxId, BlockHash)` method.
    [[#1294], [#1328]]
 -  Added `IStore.GetFirstTxIdBlockHashIndex(TxId)` method.
    [[#1294], [#1328]]
 -  Added `IStore.DeleteTxIdBlockHashIndex(TxId, BlockHash)` method.
    [[#1294], [#1328]]
 -  Added `IStore.IterateTxIdBlockHashIndex(TxId)` method.
    [[#1294], [#1328]]
 -  `Swarm<T>.StartAsync()` method became to receive `broadcastBlockInterval`
    (or `millisecondsBroadcastBlockInterval`) parameter.  [[#1351]]

### Backward-incompatible network protocol changes

### Backward-incompatible storage format changes

### Added APIs

 -  Added `BlockHash` struct.  [[#1192], [#1197]]
 -  Added `HashDigest<T>.DeriveFrom()` method.  [[#1197]]
 -  Added `BlockChain<T>.GetTxExecution()` method.  [[#1156], [#1289]]
 -  Added `StunMessage.ParseAsync(Stream, CancellationToken)` method.
    [[#1228]]
 -  Added `Swarm<T>.AddPeersAsync()` method.  [[#1234]]
 -  Added `NetMQTransport.QueryAppProtocolVersion()` static method.  [[#1235]]
 -  Added `BoundPeer.Parse()` static method.  [[#1240]]
 -  Added `TransportException` class.  [[#1242]]
 -  Added `SwarmOptions.StaticPeers` property.  [[#1230], [#1271]]
 -  Added `StaticPeers` as the last parameter to
    `RoutingTable(Address, int, int)` constructor.  [[#1230], [#1271]]
 -  Added `AtomicActionRenderer<T>` class.  [[#1267], [#1275]]
 -  Added `TxExecution` abstract class.  [[#1156], [#1289]]
 -  Added `TxSuccess` class.  [[#1156], [#1289]]
 -  Added `TxFailure` class.  [[#1156], [#1289]]
 -  Added `IExtractableException` interface.  [[#1156], [#1289]]
 -  Added `ExtractableException` static class.  [[#1156], [#1289]]
 -  Added `Address(Binary)` overloaded constructor.  [[#1289]]
 -  Added `Currency(IValue)` overloaded constructor.  [[#1289]]
 -  Added `Currency.Serialize()` method.  [[#1289]]
 -  Added `Transaction<T>.CreateUnsigned()` method.  [[#1378]]

### Behavioral changes

 -  `BlockChain<T>.Append()` now records a `TxExecution` for every single
    transaction in the appended `Block<T>`, whether a transaction is successful
    (`TxSuccess` is recorded for this case) or not (`TxFailure` is recorded
    for this case).  [[#1156], [#1289]]
 -  `ITransport.StartAsync()` and `ITransport.RunAsync()` became to throw
    `TransportException` instead of `SwarmException`.  [[#1242]]
 -  When selecting peers for `ITransport.BroadcastMessage()`,
    peers are selected from static peers in addition to peers selected
    according to existing selection methods.  [[#1230], [#1271]]
 -  `NetMQTransport` became to enforce NetMQ/[AsyncIO] to use its pure .NET
    implementation instead of Windows'
    <abbr title="input/output completion port">IOCP</abbr> when it is running
    on Mono, which powers Unity engine, since Unity does not properly
    implement the IOCP even on Windows.
    It had been done by `Swarm<T>`, but as the `ITransport` is now separated
    from it, this became done by `NetMQTransport` instead of `Swarm<T>`.
    [[#247], [#1278]]
 -  (Libplanet.RocksDBStore) `RocksDBStore.ForkBlockIndexes()` became to share
    common ancestors between forks rather than duplicating them so that much
    less space is used.  [[#1280], [#1287]]
 -  `Transaction<T>.Validate()` became to throw `InvalidTxSignatureException`
    if the transaction was not signed.  [[#1378]]

### Bug fixes

 -  Fixed a bug where executing `Transaction<T>.Actions` had not been atomic.
    `Actions` in a `Transaction<T>` now became executed all or nothing at all.
    [[#1267], [#1275]]
     -  `Transaction<T>.EvaluateActions()` method became atomic.
     -  `Transaction<T>.EvaluateActionsGradually()` method had returned
        the same number of `ActionEvaluation`s to `Transaction<T>.Actions`,
        but now became to omit the evaluations after the first action throwing
        an exception.  If no action throws any exception, it still returns
        the same number of `ActionEvaluation`s to `Transaction<T>.Actions`.
     -  State-wise, `Transaction<T>`s having any exception-throwing action
        now do not commit any changes at all to `IStateStore`.
     -  Rendering-wise, for actions following the first exception-throwing
        action, action rendering methods in `IActionRenderer<T>`
        (`RenderAction()`, `RenderActionError()`, `UnrenderAction()`, and
        `UnrenderActionError()`) became not invoked.
        If you want to dismiss all actions in unsuccessful transactions at all,
        wrap your action renderer with `AtomicActionRenderer<T>`.
 -  Fixed a bug where `KademliaProtocol.BootstrapAsync()` has sent multiple
    `Ping` messages to other peers.  [[#1219]]
 -  Fixed a bug where `KademliaProtocol.CheckReplacementCacheAsync()` has
    updated cached peers multiple times.  [[#1219]]
 -  Fixed memory leak due to undisposed `CancellationTokenRegistration`s.
    [[#1228]]
 -  Fixed a bug where `DefaultStore.Dispose()` and `TrieStateStore.Dispose()`
    had not been idempotent.  [[#1272]]
 -  (Libplanet.RocksDBStore) Fixed a bug where `RocksDBStore.Dispose()`,
    `MonoRocksDBStore.Dispose()`, and `RocksDBKeyValueStore.Dispose()` had not
    been idempotent.  [[#1272], [#1289]]
 -  Fixed a bug where `NetMQTransport` had hung forever within Mono runtime.
    [[#1278]]
 -  Fixed a bug where `DefaultStore.ForkBlockIndexes()` hadn't copied genesis
    block.  [[#1325]]
 -  (Libplanet.RocksDBStore) Fixed a bug where `RocksDBStore.GetBlock<T>()`
    and `RocksDBStore.GetTransaction<T>()` handn't returned expected values
    in multithreading environment.  [[#1339], [#1342]]

### CLI tools

 -  Added the option `--json` to `planet apv analyze` command to print result
    as JSON format.  [[#1240]]
 -  Added `planet apv query` subcommand to query app protocol version of
    specific peer. [[#1240]]
 -  Added the option `--no-passphrase` to `planet key remove` command to remove
    key without asking passphrase.  [[#1213], [#1265]]
 -  Added `planet key derive` subcommand to derive the address or
    public key from a private.  [[#1268]]
 -  Added `planet query [block-by-hash|block-by-index|tx-by-id]` commands
    to retrieve the data from the store.  [[#1284], [#1285], [#1298]]

[#1156]: https://github.com/planetarium/libplanet/issues/1156
[#1192]: https://github.com/planetarium/libplanet/issues/1192
[#1197]: https://github.com/planetarium/libplanet/pull/1197
[#1213]: https://github.com/planetarium/libplanet/issues/1213
[#1219]: https://github.com/planetarium/libplanet/pull/1219
[#1228]: https://github.com/planetarium/libplanet/pull/1218
[#1230]: https://github.com/planetarium/libplanet/issues/1230
[#1234]: https://github.com/planetarium/libplanet/pull/1234
[#1235]: https://github.com/planetarium/libplanet/pull/1235
[#1240]: https://github.com/planetarium/libplanet/pull/1240
[#1242]: https://github.com/planetarium/libplanet/pull/1242
[#1265]: https://github.com/planetarium/libplanet/pull/1265
[#1267]: https://github.com/planetarium/libplanet/issues/1267
[#1268]: https://github.com/planetarium/libplanet/pull/1268
[#1271]: https://github.com/planetarium/libplanet/pull/1271
[#1272]: https://github.com/planetarium/libplanet/pull/1272
[#1274]: https://github.com/planetarium/libplanet/pull/1274
[#1275]: https://github.com/planetarium/libplanet/pull/1275
[#1278]: https://github.com/planetarium/libplanet/pull/1278
[#1280]: https://github.com/planetarium/libplanet/issues/1280
[#1284]: https://github.com/planetarium/libplanet/issues/1284
[#1285]: https://github.com/planetarium/libplanet/issues/1285
[#1287]: https://github.com/planetarium/libplanet/pull/1287
[#1289]: https://github.com/planetarium/libplanet/pull/1289
[#1298]: https://github.com/planetarium/libplanet/pull/1298
[#1325]: https://github.com/planetarium/libplanet/pull/1325
[#1339]: https://github.com/planetarium/libplanet/issues/1339
[#1342]: https://github.com/planetarium/libplanet/pull/1342
[#1343]: https://github.com/planetarium/libplanet/pull/1343
[#1348]: https://github.com/planetarium/libplanet/pull/1348
[#1351]: https://github.com/planetarium/libplanet/pull/1351
[#1378]: https://github.com/planetarium/libplanet/pull/1378


Version 0.11.1
-------------

Released on April 22th, 2021.

 -  Fixed a bug where block synchronization had stopped due to internal
    errors. [[#1259]]

[#1259]: https://github.com/planetarium/libplanet/pull/1259

Version 0.11.0
--------------

Released on March 30, 2021.

### Backward-incompatible API changes

 -  Added the parameter `protocolVersion` to `Block<T>(long, long, BigInteger,
    Nonce, Address?, HashDigest<SHA256>?, DateTimeOffset,
    IEnumerable<Transaction<T>> transactions, HashDigest<SHA256>?,
    HashDigest<SHA256>?)` constructor.  [[#1142], [#1147], [#1162]]
 -  Added the parameter to `protocolVersion` to `Block<T>.Mine()` method.
    [[#1142], [#1147], [#1162]]
 -  Added the first parameter `protocolVersion` to `BlockHeader()` constructor.
    [[#1142], [#1147], [#1162]]
 -  Added `stagePolicy` as the second parameter to `BlockChain<T>()`
    constructor.  [[#1130], [#1131]]
 -  Added `IBlockPolicy<T>.CanonicalChainComparer` property to make
    the canonical chain.  [[#1155], [#1165], [#1184]]
 -  Added `canonicalChainComparer` as the last parameter to `BlockPolicy()`
    constructors.  [[#1155], [#1165], [#1184]]
 -  Added `canonicalChainComparer` as the second parameter to
    `DelayedRenderer()` constructor.  [[#1155], [#1165], [#1184]]
 -  Added `canonicalChainComparer` as the second parameter to
    `DelayedActionRenderer()` constructor.  [[#1155], [#1165], [#1184]]
 -  Added `reorgResistantHeight` parameter into `DelayedActionRenderer<T>()`
    constructor. [[#1163]]
 -  Added `IStore.SetBlockPerceivedTime()` method.  [[#1184]]
 -  Added `IStore.GetBlockPerceivedTime()` method.  [[#1184]]
 -  Removed `TransactionSet<T>` class.  [[#1165]]
 -  Removed `IBlockStatesStore` interface.  [[#1117]]
 -  Removed `BaseBlockStatesStore` abstract class.  [[#1117]]
 -  Removed `Swarm<T>.GetTrustedStateCompleterAsync()` method.  [[#1117]]
 -  Removed `trustedStateValidators` parameter from `Swarm<T>.PreloadAsync()`
    method.  [[#1117]]
 -  Removed `Swarm<T>.TraceTable()` method.  [[#1120]]
 -  Added `IActionContext.BlockAction` property. [[#1143]]
 -  Added nullable `TimeSpan`-typed `messageLifespan` parameter into
    `NetMQTransport()` constructor.  [[#1171]]
 -  Added `IStore.ForkTxNonces()` method.  [[#1198]]
 -  Removed `PeerState.Address` Property.  [[#1215]]
 -  `IProtocol.RebuildConnectionAsync(CancellationToken)` method was
    replaced by, `IProtocol.RebuildConnectionAsync(int, CancellationToken)`
    method.  [[#1215]]

### Backward-incompatible network protocol changes

 -  `Swarm<T>` became no longer retry when `Swarm<T>` receives
    less than 500 blocks.  [[#1112]]
 -  The existing `ChainStatus` message type (with the type number `0x24`) was
    replaced by a new `ChainStatus` message type (with the type number `0x25`).
    [[#1155], [#1165]]
 -  Removed the message types depended on features of `IBlockStatesStore`
    interface.  [[#1117]]
     -  `GetRecentStates` message type (with the type number `0x0b`)
     -  `RecentStates` message type (with the type number `0x13`)
     -  `GetBlockStates` message type (with the type number `0x22`)
     -  `BlockStates` message type (with the type number `0x23`)
 -  `Swarm<T>` became to ignore messages made earlier than a certain amount of
    time, which is configured by `SwarmOptions.MessageLifespan`.
    [[#1160], [#1171]]

### Backward-incompatible storage format changes

 -  (Libplanet.RocksDBStore) The blocks and transactions became stored in
    multiple databases.  Each block and transaction belongs to a partition
    of the database, according to its epoch unit, which is its Unix timestamp.
    Every epoch is divided by certain seconds, configured by `RocksDBStore()`
    constructor's `txEpochUnitSeconds` and `blockEpochUnitSeconds` parameters
    (86,400 by default).   [[#1183], [#1194]]
 -  (Libplanet.RocksDBStore) Continue on partitioning of database,
    `RocksDBStore()` is manage database connection by LRU Cache.
    The max size of connection cache is configured by `RocksDBStore()`
    constructor's `dbConnectionCacheSize` parameters (100
    by default).   [[#1183], [#1194]]
 -  (Libplanet.RockDBStore) The `RocksDBStore` that was previously used
    has been separated into a class called `MonoRocksDBStore`.
    Please use this class if you need to migrate.   [[#1183], [#1204]]

### Added APIs

 -  Added `Block<T>.CurrentProtocolVersion` constant.  [[#1142], [#1147]]
 -  Added `Block<T>.ProtocolVersion` property.  [[#1142], [#1147]]
 -  Added `Block<T>.Header` property.  [[#1070], [#1102]]
 -  Added `BlockHeader.ProtocolVersion` property.  [[#1142], [#1147]]
 -  Added `IBlockExcerpt` interface.  [[#1155], [#1165], [#1170]]
 -  Added `BlockExcerpt` static class.  [[#1155], [#1165], [#1170], [#1184]]
 -  `Block<T>` became to implement `IBlockExceprt` interface.
    [[#1155], [#1165], [#1170]]
 -  `BlockHeader` became to implement `IBlockExceprt` interface.
    [[#1155], [#1165], [#1170]]
 -  Added `BlockPerception` struct.  [[#1155], [#1184]]
 -  Added `BlockChain<T>.PerceiveBlock()` method.  [[#1155], [#1184]]
 -  Added `DelayedRenderer<T>.CanonicalChainComparer` and
    `DelayedActionRenderer<T>.CanonicalChainComparer` properties.
    [[#1155], [#1165], [#1184]]
 -  Added `TotalDifficultyComparer` class.  [[#1155], [#1165], [#1170], [#1184]]
 -  Added `IStagePolicy<T>` interface.  [[#1130], [#1131], [#1186]]
 -  Added `VolatileStagePolicy<T>` class.  [[#1130], [#1131], [#1136], [#1186]]
 -  Added `ITransport` interface.  [[#1052]]
 -  Added `NetMQTransport` class which implements `ITransport`.  [[#1052]]
 -  Added `Message` abstract class.  [[#1052]]
 -  Added `BlockExceedingTransactionsException` class.  [[#1104], [#1110]]
 -  Added `BlockChain<T>.GetStagedTransactionIds()` method.  [[#1089]]
 -  (Libplanet.RocksDBStore) Added `maxTotalWalSize`, `keepLogFileNum` and
    `maxLogFileSize` parameters into `RocksDBStore()` constructor.
    [[#1065], [#1102], [#1132]]
 -  Added `Swarm<T>.BlockDemand` property.  [[#1068], [#1102]]
 -  Added `BlockDemand` struct.  [[#1068], [#1102]]
 -  Added `TurnClient.PublicAddress` property.  [[#1074], [#1102]]
 -  Added `TurnClient.EndPoint` property.  [[#1074], [#1102]]
 -  Added `TurnClient.BehindNAT` property.  [[#1074], [#1102]]
 -  Added `TurnClient.InitializeTurnAsync(int, CancellationToken)` method.
    [[#1074], [#1102]]
 -  Added `TurnClient.StartAsync(int, CancellationToken)` method.
    [[#1074], [#1102]]
 -  Added `TurnClient.ReconnectTurn(int, CancellationToken)` method.
    [[#1074], [#1102]]
 -  Added `TurnClient.IsConnectable(CancellationToken)` method.
    [[#1074], [#1102]]
 -  Added `TurnClient.ReconnectTurn(CancellationToken)` method.
    [[#1074], [#1102]]
 -  Added `Libplanet.Blockchain.Renderers.Debug.RenderRecord<T>` abstract class
    and its subclasses:  [[#1119]]
     -  `RenderRecord<T>.ActionBase` abstract class
     -  `RenderRecord<T>.ActionSuccess` class
     -  `RenderRecord<T>.ActionError` class
     -  `RenderRecord<T>.BlockBase` abstract class
     -  `RenderRecord<T>.Block` class
     -  `RenderRecord<T>.Reorg` class
 -  Added `Libplanet.Blockchain.Renderers.Debug.RecordingActionRenderer<T>`
    class.  [[#1119]]
 -  Added `Libplanet.Blockchain.Renderers.Debug.ValidatingActionRenderer<T>`
    class.  [[#1119]]
 -  Added `Libplanet.Blockchain.Renderers.Debug.InvalidRenderException<T>`
    class.  [[#1119]]
 -  Added `InvalidBlockProtocolVersionException` class.  [[#1142], [#1147]]
 -  Added `InvalidBlockTxHashException` class.  [[#1116]]
 -  Added `Swarm<T>.PeerStates` property.  [[#1120]]
 -  Added `IProtocol` interface.  [[#1120]]
 -  Added `KademliaProtocol` class which implements `IProtocol`.
    [[#1120], [#1135]]
 -  Added `reorgResistantHeight` parameters into `DelayedActionRenderer<T>()`
    constructor. [[#1163]]
 -  Added `InvalidBlockPreEvaluationHashException` class.  [[#1148]]
 -  Added the parameter `validate` which is `true` by default,
    to `Transaction<T>.Deserialize()`.  [[#1149]]
 -  Added `SwarmOptions.MessageLifespan` property.  [[#1171]]
 -  Added `InvalidTimestampException` class.  [[#1171]]
 -  Added `PeerState.Peer` Property.  [[#1215]]
 -  Added `SwarmOptions.RefreshPeriod` property,
    which is 10 seconds by default.  [[#1215]]
 -  Added `SwarmOptions.RefreshLifespan` property,
    which is 60 seconds by default.  [[#1215]]

### Behavioral changes

 -  Upgraded *Bencodex* package (which is a dependency) so that Libplanet gets
    benefits from its recent optimizations.
    [[#1081], [#1084], [#1086], [#1101]]
 -  Introduced the [protocol versioning scheme][#1142].  This purposes to change
    the protocol without breaking backward compatibility.  Even the protocol
    is changed, the existing blocks made before the new protocol are guaranteed
    to behave as it had done.
    [[#1142], [#1147], [#1155] [#1162], [#1170], [#1184]]
 -  Since `BlockHeader.ProtocolVersion` was added, the existing blocks are
    considered protocol compliant with the protocol version zero.
    [[#1142], [#1147], [#1162]]
 -  When a `BlockChain<T>` follows `VolatileStagePolicy<T>`, which is
    Libplanet's the only built-in `IStagePolicy<T>` implementation at
    the moment, as its `StagePolicy`, its staged transactions are no longer
    persistent but volatile instead.  It also automatically purges staged
    transactions after the given `Lifetime`, which is 3 hours by default.
    [[#1130], [#1131], [#1136], [#1186]]
 -  `Swarm<T>` became not to receive states from trusted peers.
    [[#1061], [#1102]]
 -  `Swarm<T>` became not to retry when block downloading.  [[#1062], [#1102]]
 -  Improved performance of `BlockChain<T>.MineBlock()`.  [[#1116], [#1124]]
 -  Improved performance of `Block<T>.Deserialize()`.  [[#1116]]
 -  `Swarm<T>` became not to fill states from trusted peers, because now states
    can be validated rather than trusted due to MPT.  [[#1117]]
 -  `HashDigest<SHA256>` became serializable.  [[#795], [#1125]]
 -  `Transaction<T>()` constructors became not to validate itself.  [[#1149]]
 -  `BlockChain<T>.Append()` became to validate the given `Block<T>`
    before storing its `StateRootHash`.  [[#1172]]
 -  `Blockchain<T>` became not to stage transactions having nonce
    less than or equal to the nonce of the same signer's latest
    transaction in already mined blocks.  [[#1173], [#1180], [#1186]]
 -  Improved security of `Message.Parse()`.  [[#1161], [#1181]]
 -  Improved performance of `BlockChain<T>.Fork()`.  [[#1198]]
 -  `Swarm<T>` became not to call `KademliaProtocol.RebuildConnectionAsync()`
    right after `Swarm<T>.StartAsync()`.  If you called
    `Swarm<T>.BootstrapAsync()` before `Swarm<T>.StartAsync()`,
    peers in your table may not have you in their table right after
    `Swarm<T>.StartAsync()` (which was almost guaranteed before).  [[#1208]]
 -  Peers added during `Swarm<T>.BootstrapAsync()` before
    `Swarm<T>.StartAsync()` are now marked as stale so that
    `Swarm<T>.RefreshTableAsync()` will update.  [[#1215]]
 -  Following classes became to leave log messages with its class as logging
    context.  [[#1218]]
     -  `TrieStateStore` class
     -  `TurnClient` class
     -  `ActionEvaluation` class

### Bug fixes

 -  Fixed a bug where `BlockChain<T>.MineBlock()` was not automatically
    cancelled when the tip of the chain was changed occasionally.  [[#1141]]
 -  Fixed a bug where blocks with invalid `PreEvaluationHash` was considered
    as a valid block.  [[#1148], [#1202]]
 -  Fixed a vulnerability of the `IAccountStateDelta.TransferAsset()`'s
    internal implementation that it had doubled recipient's balance when
    a sender and a recipient is the same.
    *Since this changes the protocol, for backward compatibility, the actions
    belonging to the existing block, which was mined before the protocol v1,
    are guaranteed to still behave as it had done.  [[#1152]]
 -  Fixed a bug where `Block<T>.Evaluate()` hadn't validate its hash.  [[#1168]]
 -  Fixed memory leak due to undisposed `CancellationTokenSource`s.
    [[#1182], [#1212]]
 -  Fixed a bug where `TurnClient` hadn't released its relay connections after
    reconnecting.  [[#1185]]

### CLI tools

 -  `planet mpt diff` command became to take 4 arguments (which was 3)
    so that it can compare state root hashes from two different
    <abbr title="key–value">KV</abbr> stores.  The existing commands
    like `planet mpt diff STORE A B` do not work anymore,
    and these should be instead like `planet mpt diff STORE A STORE B`.
    [[#1129]]
 -  Store aliases used by `planet mpt` became to disallow names looking like
    URIs to disambiguate aliases from the literal store URIs.  [[#1129]]
 -  Added new subcommands `planet mpt list` and `planet mpt query`.  [[#1137]]
 -  `planet mpt diff` command became to print the differences between
    other state root hashes into stdout as JSON format.
    [[#1138], [#1191], [#1233]]

[#795]: https://github.com/planetarium/libplanet/issues/795
[#1052]: https://github.com/planetarium/libplanet/pull/1052
[#1061]: https://github.com/planetarium/libplanet/pull/1061
[#1062]: https://github.com/planetarium/libplanet/pull/1062
[#1065]: https://github.com/planetarium/libplanet/pull/1065
[#1068]: https://github.com/planetarium/libplanet/pull/1068
[#1070]: https://github.com/planetarium/libplanet/pull/1070
[#1074]: https://github.com/planetarium/libplanet/pull/1074
[#1081]: https://github.com/planetarium/libplanet/pull/1081
[#1084]: https://github.com/planetarium/libplanet/pull/1084
[#1086]: https://github.com/planetarium/libplanet/pull/1086
[#1089]: https://github.com/planetarium/libplanet/pull/1089
[#1101]: https://github.com/planetarium/libplanet/pull/1101
[#1102]: https://github.com/planetarium/libplanet/pull/1102
[#1110]: https://github.com/planetarium/libplanet/pull/1110
[#1112]: https://github.com/planetarium/libplanet/pull/1112
[#1116]: https://github.com/planetarium/libplanet/pull/1116
[#1117]: https://github.com/planetarium/libplanet/pull/1117
[#1119]: https://github.com/planetarium/libplanet/pull/1119
[#1120]: https://github.com/planetarium/libplanet/pull/1120
[#1124]: https://github.com/planetarium/libplanet/pull/1124
[#1125]: https://github.com/planetarium/libplanet/pull/1125
[#1129]: https://github.com/planetarium/libplanet/pull/1129
[#1130]: https://github.com/planetarium/libplanet/issues/1130
[#1131]: https://github.com/planetarium/libplanet/pull/1131
[#1132]: https://github.com/planetarium/libplanet/pull/1132
[#1135]: https://github.com/planetarium/libplanet/pull/1135
[#1136]: https://github.com/planetarium/libplanet/pull/1136
[#1137]: https://github.com/planetarium/libplanet/pull/1137
[#1138]: https://github.com/planetarium/libplanet/issues/1138
[#1141]: https://github.com/planetarium/libplanet/pull/1141
[#1142]: https://github.com/planetarium/libplanet/issues/1142
[#1143]: https://github.com/planetarium/libplanet/pull/1143
[#1147]: https://github.com/planetarium/libplanet/pull/1147
[#1148]: https://github.com/planetarium/libplanet/issues/1148
[#1149]: https://github.com/planetarium/libplanet/issues/1149
[#1152]: https://github.com/planetarium/libplanet/pull/1152
[#1155]: https://github.com/planetarium/libplanet/issues/1155
[#1160]: https://github.com/planetarium/libplanet/issues/1160
[#1161]: https://github.com/planetarium/libplanet/issues/1161
[#1162]: https://github.com/planetarium/libplanet/pull/1162
[#1163]: https://github.com/planetarium/libplanet/pull/1163
[#1165]: https://github.com/planetarium/libplanet/pull/1165
[#1168]: https://github.com/planetarium/libplanet/pull/1168
[#1170]: https://github.com/planetarium/libplanet/pull/1170
[#1171]: https://github.com/planetarium/libplanet/pull/1171
[#1172]: https://github.com/planetarium/libplanet/pull/1172
[#1173]: https://github.com/planetarium/libplanet/issues/1173
[#1180]: https://github.com/planetarium/libplanet/pull/1180
[#1181]: https://github.com/planetarium/libplanet/pull/1181
[#1182]: https://github.com/planetarium/libplanet/pull/1182
[#1183]: https://github.com/planetarium/libplanet/issues/1183
[#1184]: https://github.com/planetarium/libplanet/pull/1184
[#1185]: https://github.com/planetarium/libplanet/pull/1185
[#1186]: https://github.com/planetarium/libplanet/pull/1186
[#1191]: https://github.com/planetarium/libplanet/pull/1191
[#1194]: https://github.com/planetarium/libplanet/pull/1194
[#1198]: https://github.com/planetarium/libplanet/pull/1198
[#1202]: https://github.com/planetarium/libplanet/pull/1202
[#1204]: https://github.com/planetarium/libplanet/pull/1204
[#1208]: https://github.com/planetarium/libplanet/pull/1208
[#1212]: https://github.com/planetarium/libplanet/pull/1212
[#1215]: https://github.com/planetarium/libplanet/pull/1215
[#1218]: https://github.com/planetarium/libplanet/pull/1218
[#1233]: https://github.com/planetarium/libplanet/pull/1233


Version 0.10.3
--------------

Released on January 28, 2021.

-  `BlockChain<T>.MineBlock()` became to unstage transactions that have lower
   nonce than expected.  [[#1174]]

[#1174]: https://github.com/planetarium/libplanet/pull/1174


Version 0.10.2
--------------

Released on November 25, 2020.

 -  Fixed `BlockChain<T>.Append()` method's bug that it had accepted
    a `Block<T>` having more `Transactions` than the number specified by
    the `IBlockPolicy<T>.MaxTransactionsPerBlock` property.  Now it throws
    `InvalidBlockException` instead for such case.  [[#1104]]

[#1104]: https://github.com/planetarium/libplanet/pull/1104


Version 0.10.1
--------------

Released on November 24, 2020.

 -  `Transaction<T>.Id` property became lazy-loaded and cached if it's once
    loaded.  (It had been loaded when the object is instantiated.)
    [[#1079], [#1080]]
 -  The result bytes of `Transaction<T>.Serialize()` became cached
    under the hood.  [[#1079, #1080]]
 -  Fixed `BlockChain<T>.MineBlock()` method's bug which excludes one's
    all transactions virtually forever after a signer's transactions once have
    been staged without the ascending order of nonce (usually due to their
    inconsistent propagation latency on the network).  [[#1057], [#1059]]
 -  `BlockChain<T>.MineBlock()` method became to cut off staged transactions
    to mine if it takes longer than 4 seconds to collect and validate them.
    Those rest staged transactions are postponed until next block mining.
    [[#1057], [#1059]]
 -  `BlockChain<T>.ContainsBlock()` method was optimized so that it does not
    needlessly load an entire block, but looks up only an index instead.
    [[#1057], [#1059]]
 -  `BlockChain<T>` became not to validate genesis block during fork,
    where the state store is not an implementation of `IBlockStatesStore`.
    [[#1063]]
 -  Fixed a bug where `Swarm<T>.GetPeerChainStateAsync()` has thrown
    `NullReferenceException` when peers in table does failed to respond.
    [[#1066]]
 -  Fixed a bug where `BlockChain<T>` had not locked readers–writer lock for
    state changes during `MineBlock()`.  [[#1077], [#1087]]
 -  `PolymorphicAction<T>.ToString()` became more human-readable.
    [[#1085], [#1087]]
 -  Fixed a bug where `MerkleTrie` had had `MrrkleTrie.EmptyRootHash` as root
    node, which had been unable to insert new nodes.  [[#1087], [#1091]]

[#1057]: https://github.com/planetarium/libplanet/pull/1057
[#1059]: https://github.com/planetarium/libplanet/pull/1059
[#1063]: https://github.com/planetarium/libplanet/pull/1063
[#1066]: https://github.com/planetarium/libplanet/pull/1066
[#1077]: https://github.com/planetarium/libplanet/pull/1077
[#1079]: https://github.com/planetarium/libplanet/pull/1079
[#1080]: https://github.com/planetarium/libplanet/pull/1080
[#1085]: https://github.com/planetarium/libplanet/pull/1085
[#1087]: https://github.com/planetarium/libplanet/pull/1087
[#1091]: https://github.com/planetarium/libplanet/pull/1091


Version 0.10.0
--------------

Released on October 27, 2020.

### Backward-incompatible API changes

 -  Extracted rendering methods from `IAction` to `IRenderer<T>`,
    which is introduced in this version.
    From now on, rendering logic needs to be *injected* from outside
    through `BlockChain<T>.Renderers`, rather than `IAction`s knowing
    how to render themselves.
    `IRenderer<T>` also unified `BlockChain<T>.TipChanged` event,
    and introduced new events like `IActionRenderer<T>.RenderActionError()`,
    `IActionRenderer<T>.RenderBlockEnd()`, `IRenderer<T>.RenderReorg()`, and
    `IRenderer<T>.RenderReorgEnd()`.
    [[#860], [#875], [#959], [#963]]
     -  Removed `IAction.Render()` method, which was replaced by
        `IActionRenderer<T>.RenderAction()`.
     -  Removed `IAction.Unrender()` method, which was replaced by
        `IActionRenderer<T>.UnrenderAction()`.
     -  Removed `BlockChain<T>.TipChanged` event, which was replaced by
        `IRenderer<T>.RenderBlock()`.
     -  Removed `PolymorphicAction<T>.Render()` and `Unrender()` methods.
     -  Removed `BlockChain<T>.TipChangedEventArgs` class.
 -  Added methods related fungible asset states to `IAccountStateDelta`:
    [[#861], [#900], [#954]]
     -  `UpdatedFungibleAssetsAccounts` property
     -  `MintAsset(Address, Currency, BigInteger)` method
     -  `TransferAsset(Address, Address, Currency, BigInteger)` method
     -  `BurnAsset(Address, Currency, BigInteger)` method
     -  `GetBalance(Address, Currency)` method
 -  Added `IAccountStateDelta.StateUpdatedAddresses` property in order to
    distinguish state updates from asset states.  [[#861], [#900]]
 -  Added an optional parameter `AccountBalanceGetter accountBalanceGetter` to
    `Block<T>.EvaluateActionsPerTx()` method.  [[#861], [#900]]
 -  `BlockChain<T>.StageTransaction()` became to throw
    `InvalidTxGenesisHashException` when it takes a `Transaction<T>` from
    a heterogeneous `BlockChain<T>` with a different genesis block.
    [[#796], [#878]]
 -  Added `renderers` optional parameter to `BlockChain<T>()` constructor.
    [[#883], [#959], [#963]]
 -  Added `BigInteger`-typed `totalDifficulty` parameter to `Block<T>()`
    constructor.  [[#666], [#917]]
 -  Added `BigInteger`-typed `previousTotalDifficulty` parameter to
    `Block<T>.Mine()` static method.  [[#666], [#917]]
 -  Added `options` optional parameter to `Swarm<T>()` constructor.
    [[#926]]
 -  `ICryptoBackend` became to `ICryptoBackend<T>`.  [[#932]]
 -  `ICryptoBackend.Verify(HashDigest<SHA256>, byte[], PublicKey)` became to
    `ICryptoBackend<T>.Verify(HashDigest<T>, byte[], PublicKey)` [[#932]]
 -  Added `ICryptoBackend<T>.Sign(HashDigest<T>, PrivateKey)` method.
    [[#932]]
 -  `DefaultCryptoBackend` became to `DefaultCryptoBackend<T>`.  [[#932]]
 -  Added `ImmutableArray<byte>`-typed `preEvaluationHash` parameter to
    `BlockHeader` constructor. [[#931], [#935]]
 -  Added `HashDigest<SHA256>`-typed `preEvaluationHash` parameter to
    `Block<T>()` constructor. [[#931], [#935]]
 -  Replaced `SerializationInfoExtensions.GetValueOrDefault<T>()` to
    `SerializationInfoExtensions.TryGetValue<T>()`.  [[#940]]
 -  Added `bool append = true` option to both `BlockChain<T>.MineBlock()`
    overloaded methods.  Although this breaks ABI-level backward compatibility
    (i.e., you need to rebuild your assemblies), still is backward-compatible at
    API-level as the option is turned on by default.  [[#946]]
 -  Added `int? maxTransactions` option to both `BlockChain<T>.MineBlock()`
    overloaded methods.
    Although this breaks ABI-level backward compatibility (i.e., you need to
    rebuild your assemblies), still is backward-compatible at API-level as
    the option is turned on by default.  [[#1037], [#1039], [#1050]]
 -  Added `StateCompleterSet<T>? stateCompleters` option to two
    `BlockChain<T>.Append()` overloaded methods.  Although this breaks ABI-level
    backward compatibility (i.e., you need to rebuild your assemblies), still
    is backward-compatible at API-level as the option has the default value
    (`StateCompleterSet<T>.Recalculate`).  [[#946]]
 -  Added `CancellationToken cancellationToken = default(CancellationToken)`
    option to `BlockChain<T>.MineBlock(Address miner)` overloaded method.
    Although this breaks ABI-level backward compatibility (i.e., you need to
    rebuild your assemblies), still is backward-compatible at API-level as
    the option has the default value.  [[#946]]
 -  Added `IImmutableSet<Address> trustedStateValidators = null` option to both
    `Swarm<T>.StartAsync()` overloaded methods.  Although this breaks ABI-level
    backward compatibility (i.e., you need to rebuild your assemblies), still
    is backward-compatible at API-level as the option is turned on by default.
    [[#946]]
 -  Removed `Peer.AppProtocolVersion` property.  [[#949]]
 -  Removed `Peer.IsCompatibleWith()` method.  [[#949]]
 -  Replaced `Peer(PublicKey, AppProtocolVersion)` constructor with
    `Peer(PublicKey)` constructor.  [[#949]]
 -  Replaced `BoundPeer(PublicKey, DnsEndPoint, AppProtocolVersion)` constructor
    with `Peer(PublicKey, DnsEndPoint)` constructor.  [[#949]]
 -  Extracted `IStore`'s some methods dedicated to block states into
    `IBlockStatesStore`. [[#950]]
     -  `ListStateKeys()` method.
     -  `ListAllStateReferences()` method.
     -  `LookupStateReference()` method.
     -  `IterateStateReferences()` method.
     -  `StoreStateReference()` method.
     -  `ForkStateReferences()` method.
     -  `GetBlockStates()` method.
     -  `SetBlockStates()` method.
     -  `PruneBlockStates()` method.
 -  The signature of `IStore.LookupStateReference<T>(Guid, string, Block<T>)`
    method was changed to `LookupStateReference(Guid, string, long)`.  [[#950]]
 -  Added `IStateStore`-typed `stateStore` to `BlockChain<T>` constructor.
    [[#950]]
 -  Replaced `Swarm<T>.FindSpecificPeerAsync(Address, Address, int,
    BoundPeer, TimeSpan?, CancellationToken)` method with
    `Swarm<T>.FindSpecificPeerAsync(Address, int, TimeSpan?,
    CancellationToken)`.  [[#981]]
 -  Added `IActionContext.GetUnconsumedContext()` method.  [[#980]]
 -  Added `ImmutableArray<byte>`-typed `stateRootHash` parameter to
    `BlockHeader` constructor.  [[#986]]
 -  Added `HashDigest<SHA256>`-typed `stateRootHash` parameter to
    `Block<T>()` constructor.  [[#986]]
 -  Added `IBlockPolicy<T>.MaxTransactionsPerBlock` property.
    [[#1037], [#1050]]
 -  Added `IBlockPolicy<T>.GetMaxBlockBytes()` method.  [[#201], [#1050]]
 -  `IBlockPolicy<T>.DoesTransactionFollowPolicy()` method became to take
    additional `BlockChain<T>` parameter as its context.  [[#1012]]
 -  Methods in `BlockPolicy<T>` class became `virtual`.  [[#1010]]
 -  Added `int maxTransactionsPerBlock` option to both `BlockPolicy<T>()`
    overloaded constructors.  [[#1037], [#1050]]
 -  Added `int maxBlockBytes` and `int maxGenesisBytes` options to both
    `BlockPolicy<T>()` overloaded constructors.  [[#201], [#1050]]
 -  `BlockPolicy<T>()` constructor's `doesTransactionFollowPolicy` parameter
    became `Func<Transaction<T>, BlockChain<T>, bool>` on .  [[#1012]]
 -  Added `cacheSize` optional parameter to `BlockSet<T>()` constructor.
    [[#1013]]
 -  Removed `Address(SerializationInfo, StreamingContext)` constructor.
    [[#1022]]
 -  Removed constructors from `InvalidMessageException` class.  [[#1021]]

### Backward-incompatible network protocol changes

 -  The message field `RecentStates.StateReferences` became to
    `IImmutableDictionary<string, IImmutableList<HashDigest<SHA256>>>` from
    `IImmutableDictionary<Address, IImmutableList<HashDigest<SHA256>>>`.
    [[#912]]
 -  The existing `RecentStates` message type (with the type number `0x0f`) was
    replaced by a new `RecentStates` message type
    (with the type number `0x13`).  [[#912]]
 -  Added `BlockHeader.TotalDifficulty` property.  [[#666], [#917]]
 -  The existing `Pong` message type (with the type number `0x02`) was
    replaced by a new `Pong` message type
    (with the type number `0x14`).  [[#459], [#919], [#920], [#930]]
 -  The `TimestampThreshold` between `Block<T>`s was changed from 15 minutes to
    15 seconds.  [[#922], [#925]]
 -  `Swarm<T>` became to have 5 more message types:
     -  `GetChainStatus` (`0x20`)  [[#920], [#930]]
     -  `ChainStatus` (`0x24`)  [[#920], [#930], [#1003], [#1004]]
     -  `GetBlockStates` (`0x22`)  [[#946]]
     -  `BlockStates` (`0x23`)  [[#946]]
     -  `DifferentVersion` (`0x30`)  [[#949]]
 -  Every message now contains app protocol version in its header.  [[#949]]
 -  The existing `BlockHeaderMessage` message type (with the type number `0x0d`)
    was replaced by a new `BlockHeaderMessage` message type
    (with the type number `0x0c`).  [[#1003], [#1004]]
 -  Removed `PreloadBlockDownloadFailEventArgs` class.  [[#1002]]
 -  Removed `blockDownloadFailed` parameter from `Swarm<T>.PreloadAsync()`
    method.  Use `SwarmOptions.BlockDownloadTimeout` instead.  [[#1002]]

### Backward-incompatible storage format changes

 -  Added `RawTransaction<T>.GenesisHash` property.  [[#796], [#878]]
 -  Added `BlockHeader.TotalDifficulty` property.  [[#666], [#917]]

### Added APIs

 -  Added `Currency` struct.  [[#861], [#900], [#954]]
 -  Added `FungibleAssetValue` struct.  [[#861], [#944], [#954]]
 -  Added `AccountBalanceGetter` delegate.  [[#861], [#900], [#954]]
 -  Added `TurnClient.BindProxies()` method. [[#756], [#868]]
 -  Added `ActionEvaluation.Exception` property.  [[#860], [[#875]]]
 -  Added `InvalidTxGenesisHashException` class.  [[#796], [#878]]
 -  Added `InvalidBlockBytesLengthException` class.  [[#201], [#1050]]
 -  Added `CurrencyPermissionException` class.  [[#861], [#900]]
 -  Added `InsufficientBalanceException` class.  [[#861], [#900], [#954]]
 -  Added `BlockChain<T>.GetBalance()` method.  [[#861], [#900]]
 -  Added `Block<T>.TotalDifficulty` property.  [[#666], [#917]]
 -  Added `Block<T>.BytesLength` property.  [[#201], [#1050]]
 -  Added `SwarmOptions` class.  [[#926]]
 -  Added `PeerChainState` struct.  [[#936]]
 -  Added `Swarm<T>.GetPeerChainStateAsync()` method.  [[#936]]
 -  Added `Swarm<T>.LastMessageTimestamp` property.  [[#964]]
 -  Added `Block<T>.PreEvaluationHash` property.  [[#931], [#935]]
 -  Added `BlockHeader.PreEvaluationHash` property.  [[#931], [#935]]
 -  Added `Transaction<T>.BytesLength` property.  [[#201], [#1050]]
 -  Added `HashDigest(ImmutableArray<byte>)` constructor.  [[#931], [#935]]
 -  Incomplete block states became able to be handled in more flexible way.
    [[#929], [#934], [#946], [#954]]
     -  Replaced `BlockChain<T>.GetState(Address, HashDigest<SHA256>?, bool)`
        method with `GetState(Address, HashDigest<SHA256>?, StateCompleter<T>)`
        method.  Specifying `completeStates: true` and `false` can be replaced
        by `stateCompleter: StateCompleters<T>.Recalculate` and
        `StateCompleters<T>.Reject`, respectively.
     -  Replaced
        `BlockChain<T>.GetBalance(Address, Currency, HashDigest<SHA256>?, bool)`
        method with
        `GetState(Address, Currency, HashDigest<SHA256>?, StateCompleter<T>)`
        method.  Specifying `completeStates: true` and `false` can be replaced
        by `stateCompleter: FungibleAssetStateCompleters<T>.Recalculate` and
        `FungibleAssetStateCompleters<T>.Reject`, respectively.
     -  Added `StateCompleter<T>` delegate.
     -  Added `FungibleAssetStateCompleter<T>` delegate.
     -  Added `StateCompleterSet<T>` struct.
     -  Added `StateCompleters<T>` static class.
     -  Added `FungibleAssetStateCompleters<T>` static class.
     -  Added `Swarm<T>.GetTrustedStateCompleterAsync()` method.
 -  Added `IRenderer<T>` interface.  [[#959], [#963]]
 -  Added `IActionRenderer<T>` interface.  [[#959], [#967], [#970]]
 -  Added `AnonymousRenderer<T>` class.  [[#959], [#963]]
 -  Added `AnonymousActionRenderer<T>` interface.  [[#959], [#967], [#970]]
 -  Added `DelayedRenderer<T>` class.  [[#980], [#1029]]
 -  Added `DelayedActionRenderer<T>` class.  [[#980], [#1029]]
 -  Added `LoggedRenderer<T>` class.  [[#959], [#963]]
 -  Added `LoggedActionRenderer<T>` interface.  [[#959], [#967], [#970]]
 -  Added `BlockChain<T>.Renderers` property.  [[#945], [#959], [#963]]
 -  Added `BlockChain<T>.ActionRenderers` property.  [[#959], [#967], [#970]]
 -  Added `Swarm<T>.AppProtocolVersion` property.  [[#949]]
 -  `DefaultStore` became to implement `IBlockStatesStore`.  [[#950]]
 -  Added `IStateStore` interface.  [[#950]]
 -  Added `IBlockStatesStore` interface.  [[#950]]
 -  Added `TrieStateStore` class.  [[#939]]
 -  Added `ITrie` interface.  [[#939], [#1023]]
 -  Added `MerkleTrie` class.  [[#939], [#1023]]
 -  Added `IKeyValueStore` interface.  [[#939]]
 -  Added `DefaultKeyValueStore` class.  [[#939]]
 -  Added `CacheableKeyValueStore` class.  [[#939]]
 -  (Libplanet.RocksDBStore) `RocksDBStore` became to implement
    `IBlockStatesStore`.  [[#950]]
 -  (Libplanet.RocksDBStore) Added `RocksDBKeyValueStore`.  [[#939]]
 -  Added `InvalidBlockStateRootHashException` class.  [[#986]]
 -  Added `Block<T>.StateRootHash` property.  [[#986]]
 -  Added `BlockHeader.StateRootHash` property.  [[#986]]
 -  Added `MerkleTrieExtensions` static class.  [[#1023]]
 -  Added `IAccountStateDelta.PreviousStateRootHash` property to
    calculate states until previous action as state root hash.  [[#1030]]
 -  Added `UnexpectedlyTerminatedActionException.PreviousStateRootHash`
    property.  [[#1032]]

### Behavioral changes

 -  Improved performance of `Swarm<T>`.
     -  Multiplexed response and broadcast.  [[#858], [#859]]
     -  Reduced internal delays.  [[#871], [#879]]
 -  `Transaction<T>.Create()`, `Transaction<T>.EvaluateActions()` and
    `Transaction<T>.EvaluateActionsGradually()` no longer throw
    `UnexpectedlyTerminatedActionException` directly. Instead, it records
    an exception to `ActionEvaluation`s.  [[#860], [#875]]
 -  Added `Transaction<T>.GenesisHash` property.  [[#796], [#878]]
 -  Added `IAccountStateDelta.UpdatedAddresses` property contains
    asset updates besides state updates.  [[#861], [#900]]
 -  `BlockChain<T>.Append()` method became to throw
    `InvalidBlockBytesLengthException` if the given block's serialized bytes
    is longer than the limitation configured by
    `IBlockPolicy.GetMaxBlockBytes()`.  [[#201], [#1050]]
 -  `BlockChain<T>.MineBlock()` method became to cut off transactions to include
    to fit into the limitation configured by `IBlockPolicy.GetMaxBlockBytes()`.
    [[#201], [#1050]]
 -  `Swarm<T>` became to ignore received transaction with different
    genesis hash.  [[#796], [#878]]
 -  `Swarm<T>` became to ignore invalid `BlockHeader`s immediately.  [[#898]]
 -  `Swarm<T>.PreloadAsync()` became to clean up only temporary chains.
    [[#902]]
 -  `BlockPolicy<T>` became to validate `Block<T>.TotalDifficulty` property
    of a `Block<T>`.  [[#666], [#917]]
 -  `Swarm<T>` became to preload from peer that has the most difficult chain.
    [[#459], [#919]]
 -  `Swarm<T>` became to promote the most difficult chain as a canonical chain
    instead of the longest chain.  [[#459], [#919]]
 -  `Swarm<T>.BootstrapAsync()` method became not to throw `TimeoutException`
    when it fails to connect to all neighbors.  [[#933]]
 -  `Swarm<T>` became to respond to the messages with different app protocol
    version.  [[#949]]
 -  `Swarm<T>.PreloadAsync()` became to execute the actions from the branchpoint
    rather than the genesis block when there is a branch point.  [[#991]]
 -  `BlockPolicy<T>` became to validate `Block<T>.StateRootHash` property
     of a `Block<T>`.  [[#986]]
 -  `Swarm<T>` became not to sync `Block<T>`s from the peers with
    different genesis block.  [[#1003], [#1004]]
 -  `Swarm<T>` became to ignore `BlockHeaderMessage` from the peers with
    different genesis block.  [[#1003], [#1004]]
 -  `BlockChain<T>` instead of `BlockPolicy<T>` became to validate `Block<T>`s
    to append so that even if an empty implementation of `IBlockPolicy<T>` is
    used `Block<T>`s are unable to be appended to `BlockChain<T>`.  [[#1010]]
 -  `BlockSet<T>[HashDigest<SHA256>]` and `BlockChain<T>.Genesis` became cached
    so that they become faster to get.  [[#1013]]
 -  `Swarm<T>.PreloadAsync()` became to do not render blocks.  [[#1029]]

### Bug fixes

 -  Fixed a bug that `Swarm<T>` had failed to receive a request from TURN relay
    connections.  [[#404], [#871], [#890]]
 -  Fixed a bug where `Swarm<T>` had been terminated and never reconnected when
    it had been once disconnected from TURN (mostly due to [sleep mode], etc.).
    [[#909]]
 -  Fixed a bug in which pre-computed state delivery had failed when a state
    key is not an `Address` when preloading.  [[#912]]
 -  Fixed a bug where `UnexpectedlyTerminatedException` hadn't been serialized
    with `BinaryFormatter`.  [[#913]]
 -  Fixed a bug where `TurnClient` hadn't applied cancellation token to its
    connections.  [[#916]]
 -  Fixed a bug where `BlockChain<T>.GetRawState()` had overwritten block states
    without read lock.  [[#927]]
 -  Fixed a bug that `Swarm<T>` had not respond to `GetRecentStates` message
    when the target block does not exist in the chain.  [[#941]]
 -  Fixed a bug that `Swarm<T>.StartAsync()` had not worked after
    `Swarm<T>.StopAsync()` was once called.  [[#965]]
 -  Fixed a bug that `TurnClient` had thrown `InvalidOperationException` when
    reconnecting.  [[#957], [#972]]
 -  Fixed a bug that `Swarm<T>` had not received block headers after failing
    to receive previous blocks.  [[#996]]
 -  Fixed a bug that `Swarm<T>` had thrown `InvalidGenesisBlockException`
    when reorg its chain repeatedly.  [[#996]]
 -  Fixed a bug that `Swarm<T>` had propagated invalid transactions.
    [[#1043]]

### Static analyzer

 -  Introduced the *Libplanet.Analyzers* package, a Roslyn Analyzer, which
    checks if code has common mistakes prone to made with Libplanet-powered
    game apps, e.g., breaking determinism in `IAction` implementations.
    [[#1034]]

### CLI tools

 -  The `planet` command became installable using `npm`.  [[#923], [#982]]
 -  Fixed a bug that <kbd>^H</kbd> had not removed the rightmost character
    in passphrase prompts.  [[#983], [#984]]
 -  Added a new sub-command `planet mpt`.  [[#1023], [#1026]]
 -  Introduced a configuration file.  It's placed in:  [[#1023], [#1026]]
     -  Linux/macOS: *<var>$XDG_CONFIG_HOME</var>/planetarium/cli.json*
     -  Windows: *<var>%AppData%</var>\planetarium\cli.json*

[#201]: https://github.com/planetarium/libplanet/issues/201
[#404]: https://github.com/planetarium/libplanet/issues/404
[#459]: https://github.com/planetarium/libplanet/issues/459
[#666]: https://github.com/planetarium/libplanet/issues/666
[#756]: https://github.com/planetarium/libplanet/issues/756
[#796]: https://github.com/planetarium/libplanet/issues/796
[#858]: https://github.com/planetarium/libplanet/issues/858
[#859]: https://github.com/planetarium/libplanet/pull/859
[#860]: https://github.com/planetarium/libplanet/issues/860
[#861]: https://github.com/planetarium/libplanet/issues/861
[#868]: https://github.com/planetarium/libplanet/pull/868
[#871]: https://github.com/planetarium/libplanet/issues/871
[#875]: https://github.com/planetarium/libplanet/pull/875
[#878]: https://github.com/planetarium/libplanet/pull/878
[#879]: https://github.com/planetarium/libplanet/pull/879
[#883]: https://github.com/planetarium/libplanet/pull/883
[#890]: https://github.com/planetarium/libplanet/pull/890
[#898]: https://github.com/planetarium/libplanet/pull/898
[#900]: https://github.com/planetarium/libplanet/pull/900
[#902]: https://github.com/planetarium/libplanet/pull/902
[#909]: https://github.com/planetarium/libplanet/pull/909
[#912]: https://github.com/planetarium/libplanet/pull/912
[#913]: https://github.com/planetarium/libplanet/pull/913
[#916]: https://github.com/planetarium/libplanet/pull/916
[#917]: https://github.com/planetarium/libplanet/pull/917
[#919]: https://github.com/planetarium/libplanet/pull/919
[#920]: https://github.com/planetarium/libplanet/issues/920
[#922]: https://github.com/planetarium/libplanet/issues/922
[#923]: https://github.com/planetarium/libplanet/pull/923
[#925]: https://github.com/planetarium/libplanet/pull/925
[#926]: https://github.com/planetarium/libplanet/pull/926
[#927]: https://github.com/planetarium/libplanet/pull/927
[#929]: https://github.com/planetarium/libplanet/issues/929
[#930]: https://github.com/planetarium/libplanet/pull/930
[#931]: https://github.com/planetarium/libplanet/issues/931
[#932]: https://github.com/planetarium/libplanet/pull/932
[#933]: https://github.com/planetarium/libplanet/pull/933
[#934]: https://github.com/planetarium/libplanet/pull/934
[#935]: https://github.com/planetarium/libplanet/pull/935
[#936]: https://github.com/planetarium/libplanet/pull/936
[#939]: https://github.com/planetarium/libplanet/pull/939
[#940]: https://github.com/planetarium/libplanet/pull/940
[#941]: https://github.com/planetarium/libplanet/pull/941
[#944]: https://github.com/planetarium/libplanet/issues/944
[#945]: https://github.com/planetarium/libplanet/pull/945
[#946]: https://github.com/planetarium/libplanet/pull/946
[#949]: https://github.com/planetarium/libplanet/pull/949
[#950]: https://github.com/planetarium/libplanet/pull/950
[#957]: https://github.com/planetarium/libplanet/issues/957
[#959]: https://github.com/planetarium/libplanet/issues/959
[#954]: https://github.com/planetarium/libplanet/pull/954
[#963]: https://github.com/planetarium/libplanet/pull/963
[#964]: https://github.com/planetarium/libplanet/pull/964
[#965]: https://github.com/planetarium/libplanet/pull/965
[#967]: https://github.com/planetarium/libplanet/issues/967
[#970]: https://github.com/planetarium/libplanet/pull/970
[#972]: https://github.com/planetarium/libplanet/pull/972
[#980]: https://github.com/planetarium/libplanet/pull/980
[#981]: https://github.com/planetarium/libplanet/pull/981
[#982]: https://github.com/planetarium/libplanet/pull/982
[#983]: https://github.com/planetarium/libplanet/issues/983
[#984]: https://github.com/planetarium/libplanet/pull/984
[#986]: https://github.com/planetarium/libplanet/pull/986
[#991]: https://github.com/planetarium/libplanet/pull/991
[#996]: https://github.com/planetarium/libplanet/pull/996
[#1002]: https://github.com/planetarium/libplanet/pull/1002
[#1003]: https://github.com/planetarium/libplanet/issues/1003
[#1004]: https://github.com/planetarium/libplanet/pull/1004
[#1010]: https://github.com/planetarium/libplanet/pull/1010
[#1012]: https://github.com/planetarium/libplanet/pull/1012
[#1013]: https://github.com/planetarium/libplanet/pull/1013
[#1021]: https://github.com/planetarium/libplanet/pull/1021
[#1022]: https://github.com/planetarium/libplanet/pull/1022
[#1023]: https://github.com/planetarium/libplanet/pull/1023
[#1026]: https://github.com/planetarium/libplanet/pull/1026
[#1029]: https://github.com/planetarium/libplanet/pull/1029
[#1030]: https://github.com/planetarium/libplanet/pull/1030
[#1032]: https://github.com/planetarium/libplanet/pull/1032
[#1034]: https://github.com/planetarium/libplanet/pull/1034
[#1037]: https://github.com/planetarium/libplanet/pull/1037
[#1039]: https://github.com/planetarium/libplanet/pull/1039
[#1043]: https://github.com/planetarium/libplanet/pull/1043
[#1050]: https://github.com/planetarium/libplanet/pull/1050
[sleep mode]: https://en.wikipedia.org/wiki/Sleep_mode


Version 0.9.5
-------------

Released on June 12, 2020.

 -  Fixed a bug that had not properly received block hashes after the chain had
    reorged.  [[#880], [#905]]

[#905]: https://github.com/planetarium/libplanet/pull/905


Version 0.9.4
--------------

Released on June 2, 2020.

 -  (Libplanet.RocksDBStore) Fixed a bug that  `RocksDBStore.DeleteChainId()`
    method had thrown `KeyNotFoundException` when there's no such chain ID.
    [[#891]]
 -  (Libplanet.RocksDBStore) Fixed a bug that `RocksDBStore` had written logs
    into the incorrect context `DefaultContext`, not `RocksDBStore`
    the correct one.  [[#891]]

[#891]: https://github.com/planetarium/libplanet/pull/891


Version 0.9.3
-------------

Released on May 29, 2020.

 -  Fixed a `Swarm<T>.PreloadAsync()` method's bug that had hanged in a state
    downloading block hashes and finally unexpectedly terminated when a peer's
    chain had gotten reorged.   [[#880], [#884]]

[#880]: https://github.com/planetarium/libplanet/issues/880
[#884]: https://github.com/planetarium/libplanet/pull/884


Version 0.9.2
-------------

Released on May 20, 2020.

 -  (Libplanet.RocksDBStore) Fixed a memory leak bug in `RocksDBStore`.
    [[#870]]

[#870]: https://github.com/planetarium/libplanet/pull/870


Version 0.9.1
-------------

Released on May 7, 2020.

 -  Fixed a bug where the canonical chain had changed if any actions had thrown
    an exception during `Swarm<T>.PreloadAsync()`.  [[#862]]
 -  Fixed a `Swarm<T>.PreloadAsync()` method's bug that it had hung forever and
    raised `InvalidOperationException`.  [[#847], [#864]]

[#847]: https://github.com/planetarium/libplanet/issues/847
[#862]: https://github.com/planetarium/libplanet/pull/862
[#864]: https://github.com/planetarium/libplanet/pull/864


Version 0.9.0
-------------

Released on April 27, 2020.

### Backward-incompatible API changes

 -  `BaseStore` class became to implement `IDisposable`.  [[#789]]
 -  Removed `IStore.DeleteIndex(Guid, HashDigest<SHA256>)` method.  [[#802]]
 -  Extension classes was renamed.  However, it would not be affected
    if you have called it by using instance method syntax.  [[#803]]
     -  Renamed `StunAddressExtension` class to `StunAddressExtensions`.
     -  Renamed `BytesConvertExtension` class to `BytesConvertExtensions`.
     -  Renamed `RandomExtension` class to `RandomExtensions`.
     -  Renamed `AddressExtension` class to `AddressExtensions`.
     -  Renamed `HashDigestExtension` class to `HashDigestExtensions`.
     -  Renamed `NetMQFrameExtension` class to `NetMQFrameExtensions`.
     -  Renamed `NetMQSocketExtension` class to `NetMQSocketExtensions`.
     -  Renamed `SerializationInfoExtension` class to
        `SerializationInfoExtensions`.
     -  Renamed `StoreExtension` class to `StoreExtensions`.
 -  All parameters, fields, property, and method return values that had been
    represented as an `Int32` became retyped to `AppProtocolVersion`.
    [[#266], [#815]]
     -  `Swarm()` constructor's parameter `appProtocolVersion` became
        `AppProtocolVersion` (was `Int32`).
     -  `Peer()` and `BoundPeer()` constructors' parameter `appProtocolVersion`
        became `AppProtocolVersion` (was `Int32`).
     -  `Peer.AppProtocolVersion` property became `AppProtocolVersion`
        (was `Int32`).
     -  `DifferentProtocolVersionEventArgs.ExpectedVersion` and
        `DifferentProtocolVersionEventArgs.ActualVersion` properties became
        `AppProtocolVersion` (was `Int32`).
     -  Removed `DifferentAppProtocolVersionException` class.
 -  `Swarm()` constructor's `EventHandler<DifferentProtocolVersionEventArgs>
    differentVersionPeerEncountered = null` parameter became replaced by
    `DifferentAppProtocolVersionEncountered
    differentAppProtocolVersionEncountered = null` parameter.  [[#266], [#815]]
 -  Added `IEnumerable<PublicKey> trustedAppProtocolVersionSigners = null`
    parameter to `Swarm()` constructor.  [[#266], [#815]]
 -  Removed `DifferentProtocolVersionEventArgs` class.  [[#266], [#815]]
 -  Removed `createdAt` parameter from `Swarm()` constructor.  [[#838]]
 -  Replaced `BlockChain<T>.StageTransactions()` with `.StageTransaction()`
    that receives only one transaction.  [[#820]]
 -  Replaced `BlockChain<T>.UnstageTransactions()` with `.UnstageTransaction()`
    that receives only one transaction.  [[#820]]
 -  Added `IBlockPolicy.DoesTransactionFollowPolicy()` method which is a method
    to determine if a transaction follows the block policy.  [[#827]]

### Backward-incompatible network protocol changes

 -  The existing `BlockHashes` message type (with the type number `0x05`) was
    replaced by a new `BlockHashes` message type (with type number `0x0e`)
    in order to include an offset block index besides block hashes
    so that a receiver is able to determine their block indices too.
    [[#707], [#798]]
 -  `Peer` became to have 3 more fields to represent the whole fields of
    `AppProtocolVersion`, which is newly introduced.  [[#266], [#815]]
 -  The existing `RecentStates` message type (with the type number `0x0c`) was
    replaced by a new `RecentStates` message type (with type number `0x0f`)
    in order to compress its states.  [[#700], [#850]]

### Added APIs

 -  Added `AddressExtensions.ToAddress(this PrivateKey)` overloaded extension
    method.  [[#825]]
 -  Added `BlockHashDownloadState` class, a subclass of `PreloadState`.
    [[#707], [#798]]
 -  Added `BlockVerificationState` class, a subclass of `PreloadState`.
    [[#798]]
 -  Added `AppProtocolVersion` struct.  [[#266], [#815]]
 -  Added `IKeyStore` interface.  [[#831]]
 -  Added `Web3KeyStore` class.  [[#831]]
 -  Added `BlockDigest` struct.  [[#785]]
 -  Added `BlockHeader` struct.  [[#785]]
 -  Added `IStore.GetBlockDigest(HashDigest<SHA256>)` method.  [[#785]]
 -  Added `Block<T>.ToBlockDigest()` method.  [[#785]]
 -  Added `ByteArrayExtensions` class.  [[#803]]
 -  Added `IStore.PruneBlockStates<T>(Guid, Block<T>)` method.  [[#790]]
 -  Added `DifferentAppProtocolVersionEncountered` delegate.  [[#266], [#815]]
 -  Added `Swarm<T>.TrustedAppProtocolVersionSigners` property.
    [[#266], [#815]]
 -  Added `Peer.IsCompatibleWith()` method.  [[#266], [#815]]
 -  Added `TxViolatingBlockPolicyException` class.  [[#827]]
 -  Added `KeyStoreException` class.  [[#831]]
 -  Added `NoKeyException` class.  [[#831]]

### Behavioral changes

 -  `BlockChain.MineBlock()` method became to ignore transactions having
    lower nonce than the expected nonce in the chain.  [[#791]]
 -  `Swarm<T>.PreloadAsync()` and `Swarm<T>.StartAsync()` became to download
    only a list of block hashes first and then download blocks from
    simultaneously multiple peers.  [[#707], [#798]]
 -  Improved performance of `Swarm<T>` by preventing unnecessary task
    creation.  [[#817], [#837]]
 -  Improved performance of `Swarm<T>.PreloadAsync()` by parallelizing
    connections.  [[#846]]
 -  Improved response throughput of `Swarm<T>`.  [[#849]]

### Bug fixes

 -  `Swarm<T>` became not to sync the same `Block<T>`s or `Transaction<T>`s
    multiple times.  [[#784]]
 -  Fixed a `Swarm<T>`'s bug that had broadcasted a message to its source peer
    when the number of peers is not enough (less than the minimum number).
    [[#788]]
 -  Fixed a bug where `BlockChain.MineBlock()` had produced an invalid block
    when there is any staged transaction which has lower nonce than the expected
    nonce, that means, shares an already taken nonce by the same signer.
    [[#791]]
 -  Fixed a `Swarm<T>.PreloadAsync()` method's bug that temporary chain IDs
    in the store had been completely cleaned up in some corner cases
    if `cancellationToken` was requested.  [[#798]]
 -  Fixed a bug where `Swarm<T>` had crashed if it received invalid
    `Transaction<T>` from the nodes.  [[#820]]
 -  Fixed a bug where `Swarm<T>` hadn't reported `IProgress<PreloadState>`s
    correctly.[[#839]]
 -  Fixed a `Swarm<T>.PreloadAsync()` method's bug that it had hung forever
    when a block failed to be fetched due to an unexpected inner exception.
    [[#839]]
 -  Fixed a bug where actions had been evaluated twice when receiving blocks.
    [[#843], [#844]]
 -  Fixed `OverflowException` being thrown when a `passphrase` containing
    any non-ASCII characters was passed to `Pbkdf2.Derive()` method or
    `ProtectedPrivateKey.Protect()` method.  [[#845]]

### CLI tools

 -  Added the `planet` command and its alias `dotnet planet`.

[#266]: https://github.com/planetarium/libplanet/issues/266
[#700]: https://github.com/planetarium/libplanet/issues/700
[#707]: https://github.com/planetarium/libplanet/pull/707
[#784]: https://github.com/planetarium/libplanet/pull/784
[#785]: https://github.com/planetarium/libplanet/pull/785
[#788]: https://github.com/planetarium/libplanet/pull/788
[#789]: https://github.com/planetarium/libplanet/pull/789
[#790]: https://github.com/planetarium/libplanet/pull/790
[#791]: https://github.com/planetarium/libplanet/pull/791
[#798]: https://github.com/planetarium/libplanet/pull/798
[#802]: https://github.com/planetarium/libplanet/pull/802
[#803]: https://github.com/planetarium/libplanet/pull/803
[#815]: https://github.com/planetarium/libplanet/pull/815
[#817]: https://github.com/planetarium/libplanet/issues/817
[#820]: https://github.com/planetarium/libplanet/pull/820
[#825]: https://github.com/planetarium/libplanet/pull/825
[#827]: https://github.com/planetarium/libplanet/pull/827
[#831]: https://github.com/planetarium/libplanet/pull/831
[#837]: https://github.com/planetarium/libplanet/pull/837
[#838]: https://github.com/planetarium/libplanet/pull/838
[#839]: https://github.com/planetarium/libplanet/pull/839
[#843]: https://github.com/planetarium/libplanet/issues/843
[#844]: https://github.com/planetarium/libplanet/pull/844
[#845]: https://github.com/planetarium/libplanet/pull/845
[#846]: https://github.com/planetarium/libplanet/pull/846
[#849]: https://github.com/planetarium/libplanet/pull/849
[#850]: https://github.com/planetarium/libplanet/pull/850


Version 0.8.0
-------------

Released on February 4, 2020.

### Backward-incompatible API changes

 -  The internal representation for state keys became `string` (was `Address`).
    [[#368], [#774]]
     -  The return type of `IStore.GetBlockStates()` method became
        `IImmutableDictionary<string, IValue>` (was `AddressStateMap`,
        which was removed too).  [[#368], [#774]]
     -  The type of the second parameter of `IStore.SetBlockStates()` method
        became `IImmutableDictionary<string, IValue>` (was `AddressStateMap`,
        which was removed too).  [[#368], [#774]]
     -  The second parameter of `IStore.IterateStateReferences()` method became
        `string key` (was `Address address`).  [[#368], [#774]]
     -  The second parameter of `IStore.StoreStateReference()` method became
        `IImmutableSet<string> keys` (was `IImmutableSet<Address> addresses`).
        [[#368], [#774]]
     -  `IStore.ListAddresses()` method was replaced by `IStore.ListStateKeys()`
        method. [[#368], [#774]]
 -  Added `Swarm<T>.FindSpecificPeer()` method to find a specific peer given
    the address.  [[#570], [#580]]
 -  Removed `LiteDBStore` class.  Use `DefaultStore` instead.  [[#662]]
 -  Removed `BlockChain<T>.Contains(TxId)` method.
    Use `IStore.ContainsTransaction(TxId)` instead.  [[#676]]
 -  Renamed `BlockChain<T>.Contains(HashDigest<SHA256>)` method to
    `BlockChain<T>.ContainsBlock(HashDigest<SHA256>)`.  [[#678]]
 -  Removed `BlockChain<T>.Contains(Block<T>)` method.  [[#678]]
 -  Changed semantics of `BlockChain<T>.ContainsBlock(HashDigest<SHA256>)`
    method and `BlockChain<T>[HashDigest<SHA256>]` indexer as lookups only
    the current chain, not entire storage.  [[#678]]
 -  Added `IStore.ContainsBlock(HashDigest<SHA256>)` method.  [[#678]]
 -  Removed `AddressStateMap` class.  [[#98], [#368], [#692], [#774]]
     -  The return type of `BlockChain<T>.GetState()` method became `IValue`
        (was `AddressStateMap`).
     -  The return type of `IStore.GetBlockStates()` method became
        `IImmutableDictionary<string, IValue>` (was `AddressStateMap`).
     -  `IStore.SetBlockStates()` method became to take
        `IImmutableDictionary<string, IValue>` instead of `AddressStateMap`.
 -  `Swarm<T>.PreloadAsync()` method and `Swarm<T>.StartAsync()` method became
    to take `preloadBlockDownloadFailed` event handler as an argument.
    [[#694]]
 -  Added the `genesisBlock` parameter to
    `BlockChain<T>()` constructor.  [[#688]]
 -  Removed `StateReferenceDownloadState` class.  [[#703]]
 -  Removed `BlockStateDownloadState` class.  [[#703]]
 -  Removed `TxReceived` and `BlockReceived` `AsyncAutoResetEvent`s
    from `Swarm<T>`.  [[#705], [#725]]
 -  Added `workers` optional parameter into `Swarm<T>()` constructor.
    [[#613], [#727]]
 -  `Block<T>` class became not to implement `ISerializable`.  [[#751]]
 -  `Transaction<T>` class became not to implement `ISerializable`.  [[#751]]
 -  `Block<T>.ToBencodex()` became to return `Bencodex.Types.Dictionary`.
    [[#751]]
 -  `Transaction<T>.ToBencodex()` became to return `Bencodex.Types.Dictionary`.
    [[#751]]
 -  Removed `Block<T>.FromBencodex(byte[])` method.  [[#751]]
 -  Removed `Transaction<T>.FromBencodex(byte[])` method.  [[#751]]
 -  `Block<T>.ToBencodex()` became to take no arguments.  [[#749], [#757]]
 -  Removed `Swarm<T>.BroadcastBlocks(IEnumerable<Block<T>>)` method.  [[#764]]
 -  `StoreExtension.LookupStateReference<T>()` method was replaced by
    `IStore.LookupStateReference<T>()` method.  [[#722], [#774]]

### Backward-incompatible network protocol changes

 -  Added `long`-typed `offset` parameter to `RecentStates` and
    `GetRecentStates` messages.  [[#703]]
 -  Added `int`-typed `iteration` parameter to `RecentStates` message.
    [[#703]]
 -  Added `BlockHeaderMessage` message.  [[#764]]

### Backward-incompatible storage format changes

 -  The introduced `DefaultStore` is incompatible at the file-level with
    the `LiteDBStore` which had existed.  `DefaultStore` became to take
    a directory instead of a single file, and it consists of multiple
    subdirectories and a LiteDB file for indices.  [[#662], [#680]]

### Added APIs

 -  Added `DefaultStore` class to replace `LiteDBStore`.  [[#662]]
 -  Added `IStore.ListAllStateReferences<T>()` method.  [[#701], [#703]]
 -  Added `IStore.ListStateKeys()` method to replace `IStore.ListAddresses()`
    method.  [[#368], [#774]]
 -  Added `IStore.LookupStateReference<T>()` method to replace
    `StoreExtension.LookupStateReference<T>()` method.  [[#368], [#722], [#774]]
 -  Added `BlockChain<T>.Genesis` property.  [[#688]]
 -  Added `BlockChain<T>.MakeGenesisBlock()` static method.  [[#688]]
 -  Added `InvalidGenesisBlockException` class.  [[#688]]
 -  Added `StateDownloadState` class, a subclass of `PreloadState`,
    which reports state preloading iteration progress.  [[#703]]
 -  Added `PeerDiscoveryException` class which inherits `SwarmException`
    class.  [[#604], [#726]]
 -  Added `Swarm<T>.Peers` property which returns an enumerable of peers in
    `Swarm<T>`'s routing table.  [[#739]]
 -  Added `Block<T>.Serialize()` method which returns `byte[]`.  [[#751]]
 -  Added `Transaction<T>.Serialize()` method which returns `byte[]`.  [[#751]]
 -  Added `Block<T>(Bencodex.Types.Dictionary)` constructor.  [[#751]]
 -  Added `Transaction<T>(Bencodex.Types.Dictionary)` constructor.  [[#751]]
 -  Added `Block<T>.Deserialize(byte[])` method.  [[#751]]
 -  Added `Transaction<T>.Deserialize(byte[])` method.  [[#751]]
 -  Added `StoreExtension.Copy(this IStore, IStore)` extension method.  [[#753]]
 -  Added a `HashDigest<SHA256>?`-typed `TxHash` property which digests
    all transactions in the block to `Block<T>` class.  [[#749], [#757]]
 -  Added `CryptoConfig` class.  [[#758]]
 -  Added `ICryptoBackend` class.  [[#758]]
 -  Added `DefaultCryptoBackend` class.  [[#758]]
 -  Added `Swarm<T>.BroadcastBlock(Block<T>)` method.  [[#764]]
 -  Added `Swarm<T>.PeerStates` property.  [[#772]]
 -  Added `PeerState` class which represents a `Peer`s state in the
    routing table.  [[#772]]
 -  Added `Swarm<T>.CheckAllPeersAsync()` method.  [[#772]]

### Behavioral changes

 -  `Swarm<T>` became to compare only peer's addresses instead of public keys
    to determine if a peer is in routing table or not.  [[#665]]
 -  When `Swarm<T>.PreloadAsync()` method fails to download blocks,
    `Swarm<T>` became to call `preloadBlockDownloadFailed` event handler
    taken as an argument.  If the event handler is not present, `Swarm<T>`
    throws `SwarmException`.  [[#694]]
 -  `Swarm<T>.PreloadAsync()` became not to sync state references and block
    states at once.  [[#703]]
 -  `Swarm<T>` became to print less logs on debug level during sending states.
    [[#706]]
 -  Increased `Swarm<T>`'s network timeout value, in order to be stable
    a high latency internet connection.  [[#709]]
 -  `Swarm<T>.BootstrapAsync()` became to report `PeerDiscoveryException`
    instead of `SwarmException` directly. [[#604], [#726]]
 -  `BlockChain<T>.Append()` became to unstage the staged `Transaction<T>`s
    that have lower nonce than the highest nonce of the same signer's
    transactions in the same chain, since these virtually never become valid.
    [[#721], [#728]]
 -  `Swarm<T>` became not to fill blocks if received block hashes are
    continuous.  [[#732]]
 -  `Swarm<T>` became to can process more requests at once by creating TURN
    relaying proxy concurrently.  [[#744]]
 -  `Swarm<T>` became to throw `InvalidGenesisBlockException` when receiving
    block from the nodes that have a different genesis block.  [[#746]]
 -  `Swarm<T>` became to distinguish the starting stages clearly.
    In other words, `Swarm<T>.StartAsync()` became not to call
    `Swarm<T>.PreloadAsync()`.  [[#735], [#760]]
 -  The hash of `Block<T>` has changed due to the change in the method of
    serialization.  [[#762]]
 -  `Swarm<T>` became to ignore broadcasted block that has lower index than
    the current tip.  [[#764]]
 -  The way `Swarm<T>` chose peers to spread messages has changed.
    [[#765], [#767]]
     -  If there are less than 10 peers in the routing table, select all peers.
     -  If there are more than 10 peers in the routing table,
        choose one from each bucket, and if the number is less than 10,
        then select an additional peers so that the total is 10.

### Bug fixes

 -  Fixed a bug where the canonical chain could be deleted if `Swarm<T>` failed
    to download blocks due to network connection.  [[#675]]
 -  Fixed bug that re-download block from scratch in preloading.  [[#685]]
 -  Fixed a bug where state references become outdated if a chain is forked
    and then adding existing blocks into it.  [[#704]]
 -  Fixed a bug where `Swarm<T>` had exhausted all available sockets.  [[#709]]
 -  Fixed a bug where `Swarm<T>` had infinitely repeated failed requests.
    [[#709]]
 -  Fixed a bug where `Swarm<T>` hadn't stopped properly.  [[#709]]
 -  Fixed a bug where `Swarm<T>.BootstrapAsync()` had stopped due to trivial
    (recoverable) `TimeoutException`s.  [[#715], [#716]]
 -  Fixed a bug where `BlockChain<T>.GetNextTxNonce()` had returned invalid tx
    nonce.  [[#718]]
 -  Fixed a bug where mined transactions were staged again.  [[#719]]
 -  Fixed a bug where `Block<T>.Hash` property, `Block<T>.Mine()` method,
    `Block<T>.FromBencodex()` method, `Block<T>.ToBencodex()` method,
    `Transaction<T>.Id` property, `Transaction<T>.Signature` property,
    `Transaction<T>.Create()` method, `Transaction<T>.FromBencodex()` method,
    and `Transaction<T>.ToBencodex()` method had been non-deterministic on
    some `CultureInfo.CurrentCulture` (e.g., `ar_SA`, `fr_FR`, `th_TH`)
    so that it had caused network protocol incompatibilities.
    [[#734]]
 -  Fixed a bug where the states became empty between the tip of the peer to
    receive the states and the tip of the downloaded block.  [[#736]]
 -  Fixed a bug where `Swarm<T>.StartAsync()` had thrown
    `NullReferenceException` when `host` parameter is present on the outside
    of NAT.  [[#744]]
 -  Fixed a bug where `Swarm<T>` had failed to request a TURN relay when it has
    an IPv6 address.  [[#744]]
 -  Fixed a bug where `DefaultStore` had invalid state references cache after
    fork.  [[#759]]
 -  Fixed a bug where `BlockChain<T>` had rendered and evaluated actions in
    the genesis block during forking.  [[#763]]
 -  Fixed a `Swam<T>`'s bug that some `Transaction<T>`s had become excluded from
    mining `Block<T>`s after reorg from α to β where a `Transaction<T>` was once
    included by a `Block<T>` (α) and not included by an other `Block<T>` (β) for
    the same `Index` due to the latency gap between nodes.  [[#775]]
 -  Fixed a bug where `TransactionSet` and `BlockSet` has halt whole process
    when run `Trace.Assert()`.  [[#806], [#833]]

[#368]: https://github.com/planetarium/libplanet/issues/368
[#570]: https://github.com/planetarium/libplanet/issues/570
[#580]: https://github.com/planetarium/libplanet/pull/580
[#604]: https://github.com/planetarium/libplanet/issues/604
[#613]: https://github.com/planetarium/libplanet/issues/613
[#662]: https://github.com/planetarium/libplanet/pull/662
[#665]: https://github.com/planetarium/libplanet/pull/665
[#675]: https://github.com/planetarium/libplanet/pull/675
[#676]: https://github.com/planetarium/libplanet/pull/676
[#678]: https://github.com/planetarium/libplanet/pull/678
[#680]: https://github.com/planetarium/libplanet/pull/680
[#685]: https://github.com/planetarium/libplanet/pull/685
[#688]: https://github.com/planetarium/libplanet/pull/688
[#692]: https://github.com/planetarium/libplanet/pull/692
[#694]: https://github.com/planetarium/libplanet/pull/694
[#701]: https://github.com/planetarium/libplanet/pull/701
[#703]: https://github.com/planetarium/libplanet/pull/703
[#704]: https://github.com/planetarium/libplanet/pull/704
[#705]: https://github.com/planetarium/libplanet/issues/705
[#706]: https://github.com/planetarium/libplanet/pull/706
[#709]: https://github.com/planetarium/libplanet/pull/709
[#715]: https://github.com/planetarium/libplanet/issues/715
[#716]: https://github.com/planetarium/libplanet/pull/716
[#718]: https://github.com/planetarium/libplanet/pull/718
[#719]: https://github.com/planetarium/libplanet/pull/719
[#721]: https://github.com/planetarium/libplanet/issues/721
[#722]: https://github.com/planetarium/libplanet/pull/722
[#725]: https://github.com/planetarium/libplanet/pull/725
[#726]: https://github.com/planetarium/libplanet/pull/726
[#727]: https://github.com/planetarium/libplanet/pull/727
[#728]: https://github.com/planetarium/libplanet/pull/728
[#732]: https://github.com/planetarium/libplanet/pull/732
[#734]: https://github.com/planetarium/libplanet/pull/734
[#735]: https://github.com/planetarium/libplanet/issues/735
[#736]: https://github.com/planetarium/libplanet/pull/736
[#739]: https://github.com/planetarium/libplanet/pull/739
[#744]: https://github.com/planetarium/libplanet/pull/744
[#746]: https://github.com/planetarium/libplanet/pull/746
[#749]: https://github.com/planetarium/libplanet/issues/749
[#751]: https://github.com/planetarium/libplanet/pull/751
[#753]: https://github.com/planetarium/libplanet/pull/753
[#757]: https://github.com/planetarium/libplanet/pull/757
[#758]: https://github.com/planetarium/libplanet/pull/758
[#759]: https://github.com/planetarium/libplanet/pull/759
[#760]: https://github.com/planetarium/libplanet/pull/760
[#762]: https://github.com/planetarium/libplanet/pull/762
[#763]: https://github.com/planetarium/libplanet/pull/763
[#764]: https://github.com/planetarium/libplanet/pull/764
[#765]: https://github.com/planetarium/libplanet/issues/765
[#767]: https://github.com/planetarium/libplanet/pull/767
[#772]: https://github.com/planetarium/libplanet/pull/772
[#774]: https://github.com/planetarium/libplanet/pull/774
[#775]: https://github.com/planetarium/libplanet/pull/775
[#806]: https://github.com/planetarium/libplanet/issues/806
[#833]: https://github.com/planetarium/libplanet/pull/833


Version 0.7.0
-------------

Released on November 8, 2019.

### Backward-incompatible interface changes

 -  Renamed `minValue`/`maxValue` parameters to `lowerBound`/`upperBound` of
    `IRandom.Next()` methods.  [[#555], [#558]]
 -  Renamed `IStore.IterateIndex()` method to `IterateIndexes()`.
    [[#462], [#560]]
 -  `Swarm<T>` class became to implement `IDisposable` again and should be
    disposed to clean up its internal resources. [[#485]]
 -  `IStore.IterateStateReferences()` method became to receive
    `highestIndex`, `lowestIndex`, and `limit` parameters.  [[#447], [#545]]
 -  Reworked `BlockChain<T>.GetStates()` into `GetState()` which takes only
    one `Address` instead of `IEnumerable<Address>`.  [[#510], [#563]]
 -  Types of `IAction.PlainValue` and states became restricted to
    `Bencodex.Types.IValue`.  [[#541], [#552]]
     -  `IAction.LoadPlainValue(IImmutableDictionary<string, object>)` method
        became replaced by `LoadPlainValue(IValue)`.
     -  `AccountStateGetter` became to return `IValue`, not `object`.
     -  Added `BencodexExtension` static class.
 -  Removed `BlockChain<T>.Blocks`.  [[#409], [#583]]
 -  Removed `BlockChain<T>.Transactions`.  [[#409], [#583]]
 -  Removed the `linger` parameter from the `Swarm<T>()` constructor, and added
    the `waitFor` parameter to `Swarm<T>.StopAsync()` method instead.  [[#581]]
 -  Removed the `dialTimeout` parameter from the `Swarm<T>`() constructor, and
    added it to `Swarm<T>.PreloadAsync()` & `Swarm<T>.StartAsync()` methods.
    [[#581]]
 -  Removed `broadcast` parameter from `BlockChain<T>.MakeTransaction()` method.
    [[#609]]
 -  `BlockChain<T>` does not implement `IReadOnlyList<T>` anymore.  [[#630]]
     -  Added `BlockChain<T>.Count` property.  [[#630]]
     -  Removed `BlockChain<T>.LongCount()` method.  [[#630]]
     -  Removed `BlockChain<T>.Validate()` method.  [[#630]]
     -  Removed `BlockChain<T>.GetEnumerate()` method.  [[#630]]
     -  Removed `BlockPolicyExtension.ValidateBlocks()` method.  [[#630]]
     -  `IBlockPolicy<T>.GetNextBlockDifficulty()` method became to receive
        `BlockChain<T>` instead of `IReadOnlyList<Block<T>>`.  [[#630]]
     -  `IBlockPolicy<T>.ValidateNextBlock()` method became to receive
        `BlockChain<T>` instead of `IReadOnlyList<Block<T>>`.  [[#630]]

### Added interfaces

 -  Added `ProtectedPrivateKey` class.  [[#577], [#614]]
 -  Added `IncorrectPassphraseException` class.  [[#577], [#614]]
 -  Added `MismatchedAddressException` class.  [[#577], [#614]]
 -  Added `KeyJsonException` abstract class.  [[#577], [#614]]
 -  Added `InvalidKeyJsonException` class.  [[#577], [#614]]
 -  Added `UnsupportedKeyJsonException` class.  [[#577], [#614]]
 -  Added `ICipher` interface.  [[#577], [#614]]
 -  Added `Aes128Ctr` class.  [[#577], [#614]]
 -  Added `IKdf` interface.  [[#577], [#614]]
 -  Added `Pbkdf2` class.  [[#577], [#614]]
 -  Added `Scrypt` class.  [[#642], [#654]]
 -  Added `BlockChain<T>.LongCount()` method.  [[#575]]
 -  Added `BlockChain<T>[HashDigest<T>]` indexer.  [[#409], [#583]]
 -  Added `BlockChain<T>.Contains(HashDigest<T>)` method.  [[#409], [#583]]
 -  Added `BlockChain<T>.GetTransaction(TxId)` method.  [[#409], [#583]]
 -  Added `BlockChain<T>.Contains(TxId)` method.  [[#409], [#583]]
 -  Added `ByteUtil.Hex(ImmutableArray<byte>)` overloaded method.  [[#614]]
 -  Added `BlockChain<T>.Contains(Block<T>)` method.  [[#630]]
 -  Added `BlockDownloadState.SourcePeer` property.  [[#636]]

### Behavioral changes

 -  Changed to send `Pong` before updating the message sender to the routing
    table when `Ping` is received.  [[#566]]
 -  Improved performance of `StoreExtension.LookupStateReference<T>()` method.
    [[#447], [#545]]
 -  Added .NET Core 2.2 as a targeted framework.  [[#209], [#561]]
 -  `TurnClient.AcceptRelayedStreamAsync()` became to ignore disconnected
    connections.  [[#469]]
 -  `Swarm<T>.PreloadAsync()` became to ignore peers with lower tip.  [[#592]]
 -  `Swarm<T>` became to validate only stale peers.  [[#568], [#593]]
 -  `Swarm<T>` became not to check cached peers immediately after
    removing peers from its routing table. Instead, it checks cached peers
    periodically.  [[#608]]
 -  Marked `Address` and `HashDigest` as readonly.  [[#610]]
 -  `IceServer.CreateTurnClient()` became to throw `ArgumentException` when
    received invalid url.  [[#622]]
 -  `Swarm<T>` became to update peer table when receiving messages that are
    not related with [Kademlia protocol][Kademlia].  [[#594], [#627]]
 -  `Swarm<T>` became not to check least recently used peer every time when
    new peer is fetched.  [[#627]]
 -  `IAction` became guaranteed that the given
    `IActionContext.PreviousStates.GetState()` never throws
    `IncompleteBlockStatesException`. Instead, now it may calculate the
    incomplete states from the beginning if necessary.  [[#645]]
 -  `IStore.PutBlock<T>()` became to do nothing when it takes
    the `Block<T>` more than once.  [[#647]]
 -  `Swarm<T>.PreloadAsync()` became to try downloading blocks from all neighbor
    peers, even if any peer among them is unavailable to send blocks.  [[#636]]

### Bug fixes

 -  Fixed a bug where `Swarm<T>` had tried to update a peer infinitely when
    the peer is evicted from its table.  [[#566]]
 -  Fixed a bug where `Swarm<T>.AppendBlocksAsync()` re-requests blocks that
    already received when blockchain is empty.  [[#550], [#562]]
 -  Fixed a bug that `Swarm<T>` had thrown `SocketException` with a message
    `Operation on non-blocking socket would block`.  [[#405], [#485]]
 -  Fixed a bug that accessed all blocks from the genesis block when a swap
    occurred.  [[#575]]
 -  Fixed a bug that `Swarm<T>` had thrown `InvalidBlockIndexException` during
    synchronizing with other reorganized peer.  [[#528], [#576]]
 -  Fixed a bug where `Swarm<T>` does not render actions in blocks which are
    filled from other peers.  [[#579]]
 -  Fixed a bug where `Swarm<T>` renders actions in same block multiple times
    when reorg happens.  [[#579]]
 -  `LiteDBStore` became to guarantee atomicity of storing blocks. [[#584]]
 -  Fixed a bug that `BlockChain<T>` had appended a block even if fails to
    evaluate.  [[#591]]
 -  Fixed a bug where `Swarm<T>` hadn't removed stale peers.
    [[#568], [#593], [#602]]
 -  Fixed a bug that `TurnClient` had thrown `IOException` when accepting
    connection through a TURN relay server. [[#453], [#599]]
 -  Fixed a bug that `KeyNotFoundException` occurred when sending a message
    through the TurnClient.
 -  Fixed a bug where `BlockChain<T>.GetNextTxNonce` only returned the same
    nonce when transactions with an old nonce were staged.  [[#637]]
 -  Fixed a bug that `BlockChain<T>` had reset when `Swarm<T>.PreloadAsync()`
    fails.  [[#644]]
 -  Fixed bug that whole processes could halt when received an invalid
    type of message.  [[#628], [#641]]
 -  Fixed a bug that received blocks could not be processed if a branch point
    is a stale block.  [[#655]]

[#209]: https://github.com/planetarium/libplanet/issues/209
[#405]: https://github.com/planetarium/libplanet/issues/405
[#409]: https://github.com/planetarium/libplanet/issues/409
[#447]: https://github.com/planetarium/libplanet/issues/447
[#453]: https://github.com/planetarium/libplanet/issues/453
[#462]: https://github.com/planetarium/libplanet/issues/462
[#469]: https://github.com/planetarium/libplanet/pull/469
[#485]: https://github.com/planetarium/libplanet/pull/485
[#510]: https://github.com/planetarium/libplanet/issues/510
[#528]: https://github.com/planetarium/libplanet/issues/528
[#541]: https://github.com/planetarium/libplanet/issues/541
[#545]: https://github.com/planetarium/libplanet/pull/545
[#550]: https://github.com/planetarium/libplanet/issues/550
[#552]: https://github.com/planetarium/libplanet/pull/552
[#555]: https://github.com/planetarium/libplanet/issues/555
[#558]: https://github.com/planetarium/libplanet/pull/558
[#560]: https://github.com/planetarium/libplanet/pull/560
[#561]: https://github.com/planetarium/libplanet/pull/561
[#562]: https://github.com/planetarium/libplanet/pull/562
[#563]: https://github.com/planetarium/libplanet/pull/563
[#566]: https://github.com/planetarium/libplanet/pull/566
[#568]: https://github.com/planetarium/libplanet/issues/568
[#575]: https://github.com/planetarium/libplanet/pull/575
[#576]: https://github.com/planetarium/libplanet/pull/576
[#577]: https://github.com/planetarium/libplanet/issues/577
[#579]: https://github.com/planetarium/libplanet/pull/579
[#581]: https://github.com/planetarium/libplanet/pull/581
[#583]: https://github.com/planetarium/libplanet/pull/583
[#584]: https://github.com/planetarium/libplanet/pull/584
[#591]: https://github.com/planetarium/libplanet/pull/591
[#592]: https://github.com/planetarium/libplanet/pull/592
[#593]: https://github.com/planetarium/libplanet/pull/593
[#594]: https://github.com/planetarium/libplanet/issues/594
[#599]: https://github.com/planetarium/libplanet/pull/599
[#602]: https://github.com/planetarium/libplanet/pull/602
[#608]: https://github.com/planetarium/libplanet/pull/608
[#609]: https://github.com/planetarium/libplanet/pull/609
[#610]: https://github.com/planetarium/libplanet/pull/610
[#614]: https://github.com/planetarium/libplanet/pull/614
[#622]: https://github.com/planetarium/libplanet/pull/622
[#627]: https://github.com/planetarium/libplanet/pull/627
[#628]: https://github.com/planetarium/libplanet/issues/628
[#630]: https://github.com/planetarium/libplanet/pull/630
[#636]: https://github.com/planetarium/libplanet/pull/636
[#637]: https://github.com/planetarium/libplanet/pull/637
[#641]: https://github.com/planetarium/libplanet/pull/641
[#642]: https://github.com/planetarium/libplanet/issues/642
[#644]: https://github.com/planetarium/libplanet/pull/644
[#645]: https://github.com/planetarium/libplanet/pull/645
[#647]: https://github.com/planetarium/libplanet/pull/647
[#654]: https://github.com/planetarium/libplanet/pull/654
[#655]: https://github.com/planetarium/libplanet/pull/655


Version 0.6.0
-------------

Released on October 1, 2019.

### Backward-incompatible interface changes

 -  `BlockChain<T>.MineBlock()` is now `async` and became to throw
    `OperationCanceledException` if `BlockChain<T>`'s tip index is changed while
    mining.  [[#460], [#517]]
 -  Users became able to give a cancellation token to `Block<T>.Mine()` and
    `Hashcash.Answer()` to cancel the operation.  [[#460], [#517]]
 -  Replaced `UnexpectedlyTerminatedTxRehearsalException` with
    `UnexpectedlyTerminatedActionException`.  [[#498]]
 -  The following methods became to throw
    `UnexpectedlyTerminatedActionException` with having its `InnerException`
    during actions being evaluated if any action of them throws an exception:
    [[#498]]
    -  `Transaction<T>.EvaluateActions()`
    -  `Transaction<T>.EvaluateActionsGradually()`
    -  `Block<T>.EvaluateActionsPerTx()`
    -  `Block<T>.Evaluate()`
    -  `BlockChain<T>.GetStates(completeStates: true)`
 -  The concept of "namespaces" in `IStore` was replaced by "chain IDs"
    to be consistent with `BlockChain<T>`.  [[#483], [#486]]
     -  Renamed `IStore.ListNamespaces()` method to `ListChainIds()`.
     -  Renamed `IStore.DeleteNamespace()` method to `DeleteChainId()`.
     -  Renamed `IStore.GetCanonicalNamespace()` method to
        `GetCanonicalChainId()`.
     -  Renamed `IStore.SetCanonicalNamespace(string)` method to
        `SetCanonicalChainId(Guid)`.
     -  Replaced `namespace`/`sourceNamespace`/`destinationNamespace` parameters
        taking `string` of methods in `IStore` and `StoreExtension` with
        `chainId`/`sourceChainId`/`destinationChainId` taking `Guid`.
     -  Renamed `NamespaceNotFoundException` to `ChainIdNotFoundException`.
     -  Replaced `NamespaceNotFoundException(string, string)` constructor with
        `ChainIdNotFoundException(Guid, string)` constructor.
     -  Replaced `NamespaceNotFoundException.Namespace` property with
        `ChainIdNotFoundException.ChainId` property.
 -  `IStore.StoreStateReference<T>(string, IImmutableSet<Address>, Block<T>)`
    method became replaced by `StoreStateReference(Guid, IImmutableSet<Address>,
    HashDigest<SHA256>, long)` method so that it takes hash and index of
    a block instead of an entire block.  [[#420]]
 -  Added `IStore.ForkBlockIndexes()` method.  [[#420]]
 -  Removed `addressesToStrip` parameter from `IStore.ForkStateReferences<T>()`
    method.  [[#454], [#467], [#509], [#522]]
 -  Removed the concept of "staged transactions that should not be broadcasted,"
    because its primary usage had been to make a transaction of a reward action
    for a candidate for block miner, and the case became achieved through
    `IBlockPolicy<T>.BlockAction` property which was introduced at 0.5.0.
    All staged transactions became broadcasted.  [[#319], [#470]]
     -  `BlockChain<T>.StageTransactions(IDictionary<Transaction<T>, bool>)`
        method became replaced by
        `StageTransactions(IImmutableSet<Transaction<T>>)`.
     -  Removed `toBroadcast` parameter from
        `IStore.IterateStagedTransactionIds(bool)` method.
     -  `IStore.StageTransactionIds(IDictionary<TxId, bool>)` method became
        replaced by `StageTransactionIds(IImmutableSet<TxId>()`.
 -  Removed `Swarm<T>.AddPeersAsync()` method. To connect with seed peers, use
    `Swarm<T>.BootstrapAsync()` method instead.  [[#353]]
 -  `Peer` with endpoints should be typed as `BoundPeer` which is inherited from
    `Peer`.  [[#353]]
 -  Removed `IActionContext.NewGuid()` method. To get a randomly generated
    [Guid][Guid], use `RandomExtension.GenerateRandomGuid()` which implements
    [RFC 4122] instead. [[#508]]

### Added interfaces

 -  Added `BlockChain<T>.TipChanged` event which is invoked with an argument
    of `BlockChain<T>.TipChangedEventArgs` when `BlockChain<T>.Tip` is changed.
    [[#517], [#526]]
 -  Added `BlockChain<T>.TipChangedEventArgs` class.  [[#526]]
 -  Added `Swarm<T>.BootstrapAsync()` method to connect with seed peers.
    [[#353]]
 -  Added `RandomExtension` static class. [[#508]]
 -  `TxId` class became to implement `IComparable<TxId>` and
    `IComparable` interfaces.  [[#244], [#511]]

### Behavioral changes

 -  `Swarm<T>` now broadcasts transactions as soon as new transactions are
    received.  [[#463], [#496]]
 -  `Swarm<T>` now ignores block hashes which already exists.  [[#461], [#484]]
 -  `Swarm<T>.PreloadAsync()` method became to download precalculated states
    of blocks from a likely branchpoint instead of a genesis block from
    a trusted peer (i.e., `trustedStateValidators`) where there are branches
    between peers.  [[#465], [#481]]
 -  `Swarm<T>`'s internal `GetRecentStates` message became to take
    `BlockLocator`, an internal data type to approximates a path of
    a chain of blocks for heuristics to search a likely branchpoint,
    instead of `HashDigest<SHA256>`.  [[#465], [#481]]
 -  NetMQ instances are now initialized at `Swarm<T>.StartAsync()` instead of
    `Swarm<T>()`.  [[#353]]
 -  Peers now connected via [Kademlia protocol][Kademlia].
    Peers are now selectively connected to each peer.  [[#353]]
 -  `TxId`s and `Block`s are now broadcasted to selected peers from routing
    table of the host peer.  [[#353]]
 -  `PolymorphicAction<T>.ToString()` method became to show the runtime type of
    its `InnerAction` for the sake of easier debugging.  [[#512]]
 -  The order of `Block<T>.Transactions` became to be determined by
    both a `Block<T>.Hash` and a `Transaction<T>.Id`, so that signers cannot
    predict the order of transactions in a block before it's mined.
    If there are multiple transactions signed by the same signer in a block
    these transactions become grouped together and the order is determined by
    a `Block<T>.Hash` and a fingerprint derived from all these transactions,
    and transactions in each group (per signer) are ordered by
    `Transaction<T>.Nonce`.  [[#244], [#355], [#511], [#520]]
 -  `LiteDBStore()` became to create the database in memory if the `path`
    parameter is `null`.  [[#521]]

### Bug fixes

 -  Fixed a bug that `Swarm<T>` hadn't released its TURN related resources on
    `Swarm<T>.StopAsync()`.  [[#450]]
 -  Fixed a bug that `IActionContext.Random` had been possible to generated
    equivalent results between actions of different transactions in
    a `Block<T>`.  [[#519]]
 -  Fixed a bug where a forked chain would not be deleted when an exception
    occurred during fetching block from other peers.  [[#527], [#537], [#540]]

[#244]: https://github.com/planetarium/libplanet/issues/244
[#353]: https://github.com/planetarium/libplanet/pull/353
[#355]: https://github.com/planetarium/libplanet/pull/355
[#420]: https://github.com/planetarium/libplanet/pull/420
[#450]: https://github.com/planetarium/libplanet/pull/450
[#460]: https://github.com/planetarium/libplanet/issues/460
[#461]: https://github.com/planetarium/libplanet/issues/461
[#463]: https://github.com/planetarium/libplanet/issues/463
[#467]: https://github.com/planetarium/libplanet/pull/467
[#470]: https://github.com/planetarium/libplanet/pull/470
[#481]: https://github.com/planetarium/libplanet/pull/481
[#483]: https://github.com/planetarium/libplanet/issues/483
[#484]: https://github.com/planetarium/libplanet/pull/484
[#486]: https://github.com/planetarium/libplanet/pull/486
[#498]: https://github.com/planetarium/libplanet/pull/498
[#496]: https://github.com/planetarium/libplanet/pull/496
[#508]: https://github.com/planetarium/libplanet/pull/508
[#509]: https://github.com/planetarium/libplanet/issues/509
[#511]: https://github.com/planetarium/libplanet/pull/511
[#512]: https://github.com/planetarium/libplanet/pull/512
[#517]: https://github.com/planetarium/libplanet/pull/517
[#519]: https://github.com/planetarium/libplanet/pull/519
[#520]: https://github.com/planetarium/libplanet/pull/520
[#521]: https://github.com/planetarium/libplanet/pull/521
[#522]: https://github.com/planetarium/libplanet/pull/522
[#526]: https://github.com/planetarium/libplanet/pull/526
[#527]: https://github.com/planetarium/libplanet/issues/527
[#537]: https://github.com/planetarium/libplanet/pull/537
[#540]: https://github.com/planetarium/libplanet/pull/540
[Kademlia]: https://en.wikipedia.org/wiki/Kademlia
[Guid]: https://docs.microsoft.com/ko-kr/dotnet/api/system.guid?view=netframework-4.8
[RFC 4122]: https://tools.ietf.org/html/rfc4122


Version 0.5.3
-------------

Released on September 9, 2019.

### Bug fixes

 -  Fix bug where `IAccountStateDelta.GetState()` hadn't returned proper state
    when the block action is evaluated.  [[#500]]

[#500]: https://github.com/planetarium/libplanet/pull/500


Version 0.5.2
-------------

Released on August 29, 2019.

### Bug fixes

 -  Fixed a bug that `Swarm<T>.PreloadAsync()` method had thrown `LiteException`
    (or other exception depending on `IStore`), which indicates a state
    reference is duplicate, where `trustedStateValidators` is present and
    a miner tries to download precalculated states from a trusted peer.
    [[#465], [#474]]
 -  Fixed a bug tag `Swarm<T>.StartAsync()` sometimes had thrown an exception
    from `IStore` (e.g., `NullReferenceException`) during broadcasting
    transactions.  [[#352], [#476]]

[#352]: https://github.com/planetarium/libplanet/issues/352
[#465]: https://github.com/planetarium/libplanet/issues/465
[#474]: https://github.com/planetarium/libplanet/pull/474
[#476]: https://github.com/planetarium/libplanet/pull/476


Version 0.5.1
-------------

Released on August 28, 2019.

### Bug fixes

 -  Fixed a bug that `ArgumentNullException` had been thrown when a blockchain,
    which consists of incomplete states (i.e., precalculated states downloaded
    from trusted peers), encounters a new branch so that reorg is made.
    [[#454], [#466]]
 -  Fixed a bug that unnecessarily received all blocks in multiple miner
    situations.  [[#457], [#468]]

[#454]: https://github.com/planetarium/libplanet/issues/454
[#457]: https://github.com/planetarium/libplanet/issues/457
[#466]: https://github.com/planetarium/libplanet/pull/466
[#468]: https://github.com/planetarium/libplanet/pull/468


Version 0.5.0
-------------

Released on August 22, 2019.

### Backward-incompatible interface changes

 -  Added `IStore.GetBlockIndex()` method.  [[#385]]
 -  `StoreExtension.LookupStateReference<T>()` method became to return
    `Tuple<HashDigest<SHA256>, long>` which is a nullable tuple of
    `Block<T>.Hash` and `Block<T>.Index`.  [[#350]]
 -  Added `IBlockPolicy<T>.BlockAction` property.  [[#319], [#367]]
 -  Removed the type parameter of `ActionEvaluation`.  [[#319], [#367]]
 -  `ActionEvaluation.Action` became to `IAction` type.  [[#319], [#367]]
 -  `LiteDBStore()` constructor became to have a new option named `flush` and
    turned on by default.  [[#387], [LiteDB #1268]]
 -  `LiteDBStore()` constructor became to have a new option named `readOnly` and
    turned off by default.  [[#434]]
 -  `BaseIndex.ContainsKey()` method became `abstract`.  [[#390]]
 -  `BlockDownloadState.TotalBlockCount` and
    `BlockDownloadState.ReceivedBlockCount` became to `Int64` type.
    [[#396], [#399]]
 -  `IStore.IterateIndex()` method became to receive `offset` and `limit`
    parameters.  [[#425]]
 -  Added `IStore.GetCanonicalNamespace()` method.  [[#426]]
 -  Added `IStore.SetCanonicalNamespace()` method.  [[#426]]
 -  Removed `IRandom.NextDouble()` method, because [floating-point arithmetics,
    which is underspecified, likely introduce
    indeterminism][floating-point determinism].  [[#410], [#419]]
 -  Added `IActionContext.NewGuId()` method.  [[#371], [#439]]
 -  `Address(byte[])` became to throw `ArgumentNullException`
    instead of `NullReferenceException`.  [[#443]]
 -  Removed `FileStore` class.  [[#446]]

### Added interfaces

 -  Added `trustedStateValidators` option to `Swarm<T>.PreloadAsync()` method.
    If any peer in this set is reachable and there is no built up blockchain
    in a current node, `Swarm<T>` receives the latest states of the major
    blockchain from that trusted peer, which is also calculated by that peer,
    instead of autonomously calculating the states from scratch.
    Note that this option is intended to be exposed to end users through
    a feasible user interface so that they can decide whom to trust
    for themselves.
    [[#272], [#343]]
 -  Added `StoreExtension.ListAllStateReferences(this IStore, string,
    HashDigest<SHA256>?, HashDigest<SHA256>?)` extension method.
    [[#363], [#384], [#385]]
 -  `Address` class became to implement `IComparable<Address>` and
    `IComparable` interfaces.  [[#363]]
 -  Added `BlockChain<T>.BlockHashes` property.  [[#389]]
 -  `Swarm<T>.PreloadAsync(IProgress<PreloadState>, IImmutableSet<Address>,
    CancellationToken)` became to report progress for all phases.
    [[#397], [#400]]
 -  Added `PreloadState`, `ActionExecutionState`, `StateReferenceDownloadState`,
    and `BlockStateDownloadState` classes to cover all phases in the entire
    preloading process.  [[#397], [#400]]
 -  Added `Address(ImmutableArray<byte>)` constructor.  [[#442], [#443]]

### Behavioral changes

 -  `BlockChain<T>.PreloadAsync()` method became to omit rendering of
    `IAction`s in the preloaded behind blocks.  [[#272], [#343]]
 -  `Swarm<T>` became to have two more message types: `GetRecentStates` (`0x0b`)
    and `RecentStates` (`0x0c`).  [[#272], [#343]]
 -  `BlockChain<T>.MineBlock()` and `BlockChain<T>.GetNextTxNonce()` methods
    became to ignore transactions that didn't follow `Transaction<T>.Nonce`
    sequentially and treat them as pendings.  [[#365]]
 -  `BlockChain<T>` became to evaluate `IBlockPolicy<T>.BlockAction` and set the
    state when a block is appended to the chain.  [[#319], [#367]]
 -  `BlockSet<T>.ContainsKey()` and `TransactionSet<T>.ContainsKey()` methods
    became O(1) time complexity through omitting iteration and relying
    own retrieve implementations.  [[#390]]
 -  The way `LiteDBStore` stores state references became efficient,
    but the file-level backward compatibility was also broken.  [[#395], [#398]]
 -  `Swarm<T>.PreloadAsync()` method became to report a block downloading
    progress with the total number of blocks to download in the entire batch,
    instead of the window size of a chunk (i.e., 500).  [[#396], [#399]]
 -  `Swarm<T>.PreloadAsync()` became to get the first parameter, `progress`,
    which accepts `IProgress<PreloadState>`.  [[#397], [#400]]
 -  `BlockHashes` messages became to contain one more higher hash.
    [[#408], [#445]]
 -  `Swarm<T>.PreloadAsync()` became safe from data corruption even
    if a preloading process suddenly gets shutdown.  [[#417]]
 -  `FileStore` and `LiteDBStore` became to guarantee atomicity of storing
    transactions. [[#413]]
 -  `IStore.PutTransaction<T>()` became to do nothing when it takes
    the `Transaction<T>` more than once.  [[#413]]
 -  `BlockChain<T>.Swap()` became to omit common block finding when `render` is
    `false`.  [[#423]]
 -  `PrivateKey(byte[])` constructor became to check validity.  [[#438]]

### Bug fixes

 -  Fixed a bug where the `LiteDBStore.IterateStagedTransactionIds()` returns
    duplicated transaction ids.  [[#366]]
 -  Fixed a bug that `NullReferenceException` occurred when serializing default
    `Address`.  [[#369]]
 -  Removed unnecessary mutex in `Swarm<T>` to avoid continuous delays in peer
    registration in some situations.  [[#375]]
 -  Fixed a bug that `TurnClient` had thrown `KeyNotFoundException` and
    `IOException` on startup.  [[#377], [#378]]
 -  Fixed a `LiteDBStore` bug that blocks or transactions had got corrupted
    sometimes.  Instead, `LiteDBStore.GetTransaction()` became possible to
    return `null` even for already stored transactions, and for that case,
    a warning will be logged through Serilog.
    [[#386], [#387], [LiteDB #1268]]
 -  Fixed a bug that `NetworkStreamProxy.StartAsync()` hadn't stopped properly
    when the connection had reset by a remote peer.  [[#414]]
 -  Fixed a bug that `Swarm<T>` had hung forever after a remote peer had
    disconnected while receiving.  [[#416]]
 -  Fixed a bug that `Swarm<T>.PreloadAsync()` had been processed even if there
    is no appropriate peer. [[#418]]
 -  Fixed a bug that TURN-related tasks hadn't restarted automatically when an
    exception occurred.  [[#422]]
 -  Fixed a bug that TURN relay connection had disconnected when preloading
    took a long time.  [[#424]]

[#319]: https://github.com/planetarium/libplanet/issues/319
[#343]: https://github.com/planetarium/libplanet/pull/343
[#350]: https://github.com/planetarium/libplanet/pull/350
[#363]: https://github.com/planetarium/libplanet/pull/363
[#365]: https://github.com/planetarium/libplanet/pull/365
[#366]: https://github.com/planetarium/libplanet/pull/366
[#367]: https://github.com/planetarium/libplanet/pull/367
[#369]: https://github.com/planetarium/libplanet/pull/369
[#371]: https://github.com/planetarium/libplanet/issues/371
[#375]: https://github.com/planetarium/libplanet/pull/375
[#377]: https://github.com/planetarium/libplanet/issues/377
[#378]: https://github.com/planetarium/libplanet/pull/378
[#384]: https://github.com/planetarium/libplanet/issues/384
[#385]: https://github.com/planetarium/libplanet/pull/385
[#386]: https://github.com/planetarium/libplanet/pull/386
[#387]: https://github.com/planetarium/libplanet/pull/387
[#389]: https://github.com/planetarium/libplanet/pull/389
[#390]: https://github.com/planetarium/libplanet/pull/390
[#395]: https://github.com/planetarium/libplanet/issues/395
[#396]: https://github.com/planetarium/libplanet/issues/396
[#397]: https://github.com/planetarium/libplanet/issues/397
[#398]: https://github.com/planetarium/libplanet/pull/398
[#399]: https://github.com/planetarium/libplanet/pull/399
[#400]: https://github.com/planetarium/libplanet/pull/400
[#408]: https://github.com/planetarium/libplanet/issues/408
[#410]: https://github.com/planetarium/libplanet/issues/410
[#413]: https://github.com/planetarium/libplanet/pull/413
[#414]: https://github.com/planetarium/libplanet/pull/414
[#416]: https://github.com/planetarium/libplanet/pull/416
[#417]: https://github.com/planetarium/libplanet/pull/417
[#418]: https://github.com/planetarium/libplanet/pull/418
[#419]: https://github.com/planetarium/libplanet/pull/419
[#422]: https://github.com/planetarium/libplanet/pull/422
[#423]: https://github.com/planetarium/libplanet/pull/423
[#424]: https://github.com/planetarium/libplanet/pull/424
[#426]: https://github.com/planetarium/libplanet/pull/426
[#434]: https://github.com/planetarium/libplanet/pull/434
[#438]: https://github.com/planetarium/libplanet/pull/438
[#439]: https://github.com/planetarium/libplanet/pull/439
[#442]: https://github.com/planetarium/libplanet/issues/442
[#443]: https://github.com/planetarium/libplanet/pull/443
[#445]: https://github.com/planetarium/libplanet/pull/445
[#446]: https://github.com/planetarium/libplanet/pull/446
[LiteDB #1268]: https://github.com/mbdavid/LiteDB/issues/1268
[floating-point determinism]: https://wp.me/p1fTCO-kT


Version 0.4.1
-------------

Released on July 11, 2019.

### Bug fixes

 -  Fixed a bug where the `BlockChain<T>.GetStates()` method had not returned
    the latest state when there are multiple addresses.  [[#346]]

[#346]: https://github.com/planetarium/libplanet/pull/346


Version 0.4.0
-------------

Released on July 8, 2019.

### Backward-incompatible interface changes

 -  `Peer.AppProtocolVersion` became nullable to represent `Peer` whose version
    is unknown.  [[#280]]
 -  Added `IStore.ListAddresses()` method.  [[#272], [#285]]
 -  Added `IStore.ListTxNonces()` method. [[#272], [#309], [#310]]
 -  Removed `BlockChain<T>.GetNonce()` method.  [[#294]]
 -  `BlockChain<T>.StageTransactions` became to receive
    `IDictionary<Transaction<T>, bool>` instead of `ISet<Transaction<T>>`.
    [[#274], [#297]]
 -  `IStore.StageTransactionIds()` method became to receive
    `IDictionary<TxId, bool>` instead of `ISet<TxId>`.  [[#274], [#297]]
 -  `IStore.IterateStagedTransactionIds()` method became to receive
    `bool toBroadcast` which is whether to iterate only the TxId set to
    broadcast.  [[#274], [#297]]
 -  `Swarm<T>.StartAsync()` method became to receive `broadcastTxInterval`
    (or `millisecondsBroadcastTxInterval`) parameter.  [[#274], [#297]]
 -  `IStore` became to treat a "tx nonce" mere a `long` integer instead of
    a stack of block hashes.  [[#272], [#307], [#309], [#310]]
     -  `IStore.IncreaseTxNonce<T>(string, Block<T>)` method was replaced by
        `IStore.IncreaseTxNonce(string, Address, long)` method.
     -  Removed `IStore.ForkTxNonce()` method.
     -  `FileStore` became to occupy fewer bytes for storing tx nonces.
        This change broke file-level backward compatibility.
 -  `IStore` became possible to look up multiple state references in a stack.
    [[#272], [#307]]
     -  Removed `IStore.LookupStateReference<T>()` method.
        Instead, a newly added static class `StoreExtension` provides
        an extension method of the same name.
     -  Added `IStore.IterateStateReferences()` method.
 -  `Swarm` became to have type parameter `T` to represent an action type as
    like as `BlockChain<T>`.  [[#324]]
 -  `Swarm<T>` constructor became to receive `BlockChain<T>`.  [[#324]]
 -  Methods  in `Swarm<T>` that had taken a parameter of `BlockChain<T>` type
    became to neither longer take `BlockChain<T>` nor a generic method.
    Because the `Swarm<T>` constructor takes it instead.  [[#324]]
 -  `Swarm<T>` does not implement `ICollection<Peer>` anymore.  [[#326]]
 -  Added `IStore.DeleteNamespace()` method. [[#329]]
 -  Removed the `id` parameter from the `BlockChain<T>` constructor, and it
    became to automatically detect an appropriate `BlockChain<T>.Id`.
    [[#279], [#332]]

### Added interfaces

 -  Added `LiteDBStore` backend that uses [LiteDB] under the hood.  [[#269]]
 -  All `*Async()` methods belonging to `TurnClient` class became to have
    `cancellationToken` option.  [[#287]]
 -  Added a `Peer` constructor omitting `appProtocolVersion` parameter
    to create a `Peer` whose version is unknown.  [[#280]]
 -  Added `IncompleteBlockStatesException` class.  [[#272], [#285]]
 -  Added `completeStates` option to `BlockChain<T>.GetStates()` method.
    [[#272], [#285]]
 -  Added `BlockChain<T>.MakeTransaction(PrivateKey, IEnumerable<T>,
    IImmutableSet<Address>, DateTimeOffset?)` method.  [[#294]]
 -  Added `BlockChain<T>.GetNextTxNonce()` method which counts staged
    transactions too during nonce computation.  [[#270], [#294]]
 -  Added `StoreExtension` static class.  [[#272], [#307]]
 -  Added `Swarm<T>.BlockChain` property.  [[#272], [#343]]

### Behavioral changes

 -  `BlockChain<T>.GetStates()` method became to throw
    `IncompleteBlockStatesException` if its `Store` lacks the states of a block
    that a requested address lastly updated.  [[#272], [#285]]
 -  A message `Swarm<T>` makes became to have multiple blocks within it, which
    means round trips on the network are now much reduced.  [[#273], [#276]]
 -  `Message.Block` has been replaced by `Message.Blocks` and the magic number
    has been changed to `0x0a`.  [[#276]]
 -  Improved performance of `Swarm<T>`'s response time to `GetBlockHashes`
    request messages.  [[#277]]
 -  Added IPv6 support to `Libplanet.Stun.StunAddress`. [[#267], [#271]]
 -  `IStore.GetBlockStates()` became able to return `null` to represent
    an absence of states (i.e., incomplete states).  [[#272], [#285]]
 -  `Swarm<T>` became to broadcast staged `Transaction`s periodically
     so that game apps no more need to maintain their own thread to
     broadcast staged transactions.  [[#274], [#297]]
 -  Previously, `Swarm<T>` had sent an empty `GetTxs` message when it receives
    an empty `TxIds` from peers, and it had made the network waste bandwidth for
    unnecessary messages.  `Swam<T>` became to no more send such empty `GetTxs`.
    [[#297]]
 -  `BlockChain<T>.Swap()` became to delete an index, tx nonces, and state
    references in the replaced chain. [[#329]]
 -  Reduced the memory footprint of `BlockChain<T>.FindBranchPoint()` method
    under the circumstances that the height of
    the `BlockChain<T>` object is high.  [[#282], [#299]]

### Bug fixes

 -  Fixed a bug that `Swarm<T>` reported `TaskCanceledException` as an unknown
    exception while stopping. [[#275]]
 -  Fixed a bug that `Swarm<T>` didn't stop properly during
    `Swarm<T>.PreloadAsync()`. [[#275]]
 -  Fixed a bug where the oldest `TxNonce` of an address is not invalidated
    when forking using `FileStore.ForkTxNonce()` method.  [[#281]]
 -  Fixed a bug where `LiteDBStore.GetTxNonce()` method throws a
    `System.IO.IOException` after forking.  [[#281]]
 -  Fixed a bug that `TurnClient` had not stopped properly.  [[#287]]
 -  Fixed a bug that `TurnClient` had been trying to use an already closed
    connection. [[#303], [#308]]
 -  Fixed a bug that `KeyNotFoundException` had been thrown instead of
    `ArgumentOutOfRangeException` when `Blockchain<T>[int]` called while the
    index of a block that does not exist locally.  [[#208], [#317]]
 -  Fixed a bug that `Swarm<T>` had not dial to other peer after
    `Swarm<T>.PreloadAsync()`.  [[#311]]
 -  Fixed an issue where unknown exceptions occurred when `Swarm<T>` receiving
    a message.  [[#321], [#327]]

[LiteDB]: https://www.litedb.org/
[#208]: https://github.com/planetarium/libplanet/issues/208
[#267]: https://github.com/planetarium/libplanet/issues/267
[#269]: https://github.com/planetarium/libplanet/pull/269
[#270]: https://github.com/planetarium/libplanet/pull/270
[#271]: https://github.com/planetarium/libplanet/pull/271
[#272]: https://github.com/planetarium/libplanet/issues/272
[#273]: https://github.com/planetarium/libplanet/issues/273
[#274]: https://github.com/planetarium/libplanet/issues/274
[#275]: https://github.com/planetarium/libplanet/pull/275
[#276]: https://github.com/planetarium/libplanet/pull/276
[#277]: https://github.com/planetarium/libplanet/pull/277
[#279]: https://github.com/planetarium/libplanet/issues/279
[#280]: https://github.com/planetarium/libplanet/pull/280
[#281]: https://github.com/planetarium/libplanet/pull/281
[#282]: https://github.com/planetarium/libplanet/issues/282
[#285]: https://github.com/planetarium/libplanet/pull/285
[#287]: https://github.com/planetarium/libplanet/pull/287
[#294]: https://github.com/planetarium/libplanet/pull/294
[#297]: https://github.com/planetarium/libplanet/pull/297
[#299]: https://github.com/planetarium/libplanet/pull/299
[#303]: https://github.com/planetarium/libplanet/issues/303
[#307]: https://github.com/planetarium/libplanet/pull/307
[#308]: https://github.com/planetarium/libplanet/pull/308
[#309]: https://github.com/planetarium/libplanet/issues/309
[#310]: https://github.com/planetarium/libplanet/pull/310
[#311]: https://github.com/planetarium/libplanet/pull/311
[#317]: https://github.com/planetarium/libplanet/pull/317
[#321]: https://github.com/planetarium/libplanet/pull/321
[#324]: https://github.com/planetarium/libplanet/pull/324
[#326]: https://github.com/planetarium/libplanet/pull/326
[#327]: https://github.com/planetarium/libplanet/pull/327
[#329]: https://github.com/planetarium/libplanet/pull/329
[#332]: https://github.com/planetarium/libplanet/pull/332

Version 0.3.0
-------------

Released on May 31, 2019.

### Backward-incompatible interface changes

 -  Added `IAction.Render(IActionContext, IAccountStateDelta)` method.
    [[#31], [#212]]
 -  Added `IAction.Unrender(IActionContext, IAccountStateDelta)` method.
    [[#31], [#212]]
 -  `BlockChain<T>.Validate()` method became to receive
    `IReadOnlyList<Block<T>>` instead of `IEnumerable<Block<T>>`.  [[#205]]
 -  `IBlockPolicy<T>.GetNextBlockDifficulty()` method became to receive
    `IReadOnlyList<Block<T>>` instead of `IEnumerable<Block<T>>`.  [[#205]]
 -  Added
    `IBlockPolicy<T>.ValidateNextBlock(IReadOnlyList<Block<T>>, Block<T>)`
    method.  [[#210]]
 -  Removed `IBlockPolicy<T>.ValidateBlocks()` method.  [[#210]]
 -  `BlockChain<T>[int]` became to throw `ArgumentOutOfRangeException` instead
    of `IndexOutOfRangeException`.  [[#210]]
 -  Removed `KeyEquals()` methods from all classes and structs.  [[#216]]
 -  `Swarm` class now does not implement `IEquatable<Swarm>` anymore and
    its `Equals(object)` method and `GetHashCode()` method became to have
    default behavior of `object` class.  [[#216]]
 -  Also, `Swarm` class now does not implement `IDisposable` too. Thus
    `Swarm.Dispose()` was removed too. [[#218]]
 -  `Swarm` became to use a queue to maintain internal messages.  [[#218]]
     -  The broadcasting methods are no more `async`, so they are renamed
        as below.
        -  `Swarm.BroadcastBlocksAsync()` → `Swarm.BroadcastBlocks()`
        -  `Swarm.BroadcastTxsAsync()` → `Swarm.BroadcastTxs()`
 -  The type of `Block<T>.Difficulty` is changed to `long` instead of `int`, and
    related classes method parameters and field types have changed accordingly.
 -  Removed `HashDigest.HasLeadingZeroBits()` method.  [[#213]]
 -  The signature of `IStore.PutBlock<T>(Block<T>)` method was changed to
    `PutBlock<T>(Block<T>, Address)`.  [[#189], [#197]]
 -  `Block<T>.Hash` is no longer calculated using the full data of the
    `Transaction<T>`, but is calculated using only the `Transaction<T>.Id`.
    [[#234]]
 -  Added `IStore.LookupStateReference<T>(string, Address, Block<T>)` method.
    [[#232]]
 -  Added `IStore.StoreStateReference<T>(string, Block<T>)` method.
    [[#232]]
 -  Added `IStore.ForkStateReferences<T>(string, string, Block<T>,
    IImmutableSet<Address>` method.  [[#232]]
 -  Removed `Block<T>.Validate()` and `Block<T>.EvaluateActions()` method.
    [[#243]]
 -  Added `Transaction<T>.Nonce` and `RawTransaction.Nonce` properties.
    [[#246]]
 -  Added `IStore.GetTxNonce(string, Address)` method.  [[#246]]
 -  Added `IStore.IncreaseTxNonce<T>(string, Block<T>)` method.  [[#246]]
 -  Added `IStore.ForkTxNonce<T>(string, string, Block<T>,
    IImmutableSet<Address>` method.  [[#246]]

### Added interfaces

 -  `BlockChain<T>` became to implement `IReadOnlyList<Block<T>>`.  [[#205]]
 -  Added `Swarm.DifferentVersionPeerEncountered` event handler that can handle
    events when a different version of a peer is discovered.  [[#167]], [[#185]]
 -  Added `Peer.AppProtocolVersion` property.  [[#185]]
 -  Added `Swarm.PreloadAsync()` method to explicitly and preemptively download
    initial blocks before `Swarm.StartAsync<T>()` being called.
    [[#204]], [[#206]]
 -  Added `BlockDownloadState` class to represent a block downloading state.
    [[#204]], [[#206]]
 -  Added `BlockPolicyExtension.ValidateBlocks<T>(IBlockPolicy<T>,
    IReadOnlyList<Block<T>>, DateTimeOffset)` method.  [[#210]]
 -  Added `Transaction<T>.EvaluateActionsGradually(HashDigest<SHA256>, long,
    IAccountStateDelta, Address, bool)` method.  [[#31], [#212]]
 -  Added `Block<T>.EvaluateActionsPerTx(AccountStateGetter)` method.
    [[#31], [#212]]
 -  Added `HashDigest.Satisfies()` method.  [[#213]]
 -  `BlockPolicy<T>` constructor became to receive the `minimumDifficulty`
    and the mining `difficultyBoundDivisor`.  [[#213]]
 -  Added `BlockChain<T>.UnstageTransactions()` method.  [[#223]]
 -  `Swarm` constructor became to receive a `linger` (or `millisecondsLinger`)
    parameter.  This purposes to determine how long to wait for pending
    messages when a `Swarm` instance is requested to terminate.
 -  Added `NamespaceNotFoundException` class.  [[#232]]
 -  Added `Block<T>.Evaluate()` method.  [[#243]]
 -  Made `InvalidBlockTimestampException` class `public` so that it can be
    caught. [[#133], [#251]]
 -  Added `InvalidTxNonceException` class.  [[#246]]

### Behavioral changes

 -  `Swarm.StartAsync()` now receives the height of blocks (tip `Index`) from
    other known peers and synchronizes the blocks if necessary
    before propagating/receiving pinpointed recent blocks to prevent inefficient
    round-trips.  [[#187], [#190]]
 -  The calculation algorithm of `BlockPolicy<T>.GetNextBlockDifficulty()`
    method was changed to the [Ethereum Homestead algorithm] except for the
    difficulty bomb.  [[#213]]
 -  The difficulty was changed from representing the number of leading zeros of
    target number to representing a divisor to obtain the target number.
    [[#213]]
 -  `BlockSet<T>[int]` changed so as not to validate a block.  [[#231]]
 -  Improved read performance of `Block<T>.Hash` and `Transaction<T>.Id`.
    [[#228], [#234]]
 -  `Swarm.StartAsync()` now does not call `Swarm.StopAsync()` anymore,
    therefore `Swarm.StopAsync()` should be explicitly called.  [[#236]]
 -  `Transaction<T>.EvaluateActionsGradually()` became to record
    `IAccountStateDelta.SetState()` calls even if its argument is the same
    to the previous state. [[#241]]
 -  `Block<T>.Validate()` and `Block<T>.EvaluateActions()` are integrated into
    `Block<T>.Evaluate()`.  [[#243]]
 -  `BlockChain<T>.Append()` became to execute `Action.Execute()` only once per
    action in the `Block<T>`.  [[#243]]
 -  `BlockChain<T>.Append()` method became to throw `InvalidTxNonceException`
    when the `Transaction<T>.Nonce` does not correspond to its `Signer`'s
    current nonce.  [[#246]]
 -  `Swarm` became to enforce `ForceDotNet.Force()` in [AsyncIO] while
    it's running on Mono runtime.  [[#247]]

### Bug fixes

 -  Fixed a bug that TURN relay had been disconnected when being connected for
    longer than 5 minutes.  [[#198]]
 -  Fixed a bug that `Swarm` had attempted to use TURN relay even if the `host`
    argument was given.  [[#198]]
 -  Improved the read throughput of `BlockChain<T>.Append()`.
 -  Improved overall read throughput of `BlockChain<T>` while blocks are being
    mined by `BlockChain<T>.MineBlock()`.  [[#191]]
 -  Fixed a bug that `TurnClientException` had been thrown by Swarm when a STUN
    nonce is stale.  [[#193]]
 -  Fixed `BlockChain<T>.GetStates()` had descended to the bottom
    (i.e., the genesis block) where a given `Address` refers to
    a nonexistent account (i.e., never used before).  [[#189], [#192]]
 -  Fixed a bug that a TURN connection had turned unavailable after
    it once failed to parse a message (due to a corrupted packet).
    [[#215]]
 -  Instead of validating the entire blocks, `BlockChain<T>.Append()` method
    became to validate only the next block to be appended.  [[#210]]
 -  Improved `BlockChain<T>.Fork()` performance by avoiding double validation
    of already validated blocks.  [[#215]]
 -  Removed unnecessary writer locks on `BlockChain<T>.StageTransactions()`.
    [[#217]]
 -  Improved concurrency of `BlockChain<T>.Append()` method by removing
    unnecessary race conditions. [[#217]]
 -  Fixed a bug that `Swarm` could not properly communicate with `Peer` behind
    NAT. [[#240]]
 -  Fixed a bug that `BlockChain<T>.FindNextHashes()` throws
    `ArgumentOutOfRangeException` when chain is empty.
 -  Fixed a bug that `TurnClient.AcceptRelayedStreamAsync()`didn't handle
    concurrent connections correctly. [[#256]]

[AsyncIO]: https://github.com/somdoron/AsyncIO
[Ethereum Homestead algorithm]: https://github.com/ethereum/EIPs/blob/master/EIPS/eip-2.md
[#31]: https://github.com/planetarium/libplanet/issues/31
[#133]: https://github.com/planetarium/libplanet/issues/133
[#185]: https://github.com/planetarium/libplanet/pull/185
[#187]: https://github.com/planetarium/libplanet/issues/187
[#190]: https://github.com/planetarium/libplanet/pull/190
[#191]: https://github.com/planetarium/libplanet/pull/191
[#193]: https://github.com/planetarium/libplanet/pull/193
[#197]: https://github.com/planetarium/libplanet/pull/197
[#198]: https://github.com/planetarium/libplanet/pull/198
[#204]: https://github.com/planetarium/libplanet/issues/204
[#205]: https://github.com/planetarium/libplanet/pull/205
[#206]: https://github.com/planetarium/libplanet/pull/206
[#210]: https://github.com/planetarium/libplanet/pull/210
[#212]: https://github.com/planetarium/libplanet/pull/212
[#213]: https://github.com/planetarium/libplanet/pull/213
[#215]: https://github.com/planetarium/libplanet/pull/215
[#216]: https://github.com/planetarium/libplanet/pull/216
[#217]: https://github.com/planetarium/libplanet/pull/217
[#218]: https://github.com/planetarium/libplanet/pull/218
[#223]: https://github.com/planetarium/libplanet/pull/223
[#228]: https://github.com/planetarium/libplanet/issues/228
[#231]: https://github.com/planetarium/libplanet/pull/231
[#232]: https://github.com/planetarium/libplanet/pull/232
[#234]: https://github.com/planetarium/libplanet/pull/234
[#236]: https://github.com/planetarium/libplanet/pull/236
[#240]: https://github.com/planetarium/libplanet/pull/240
[#241]: https://github.com/planetarium/libplanet/pull/241
[#243]: https://github.com/planetarium/libplanet/pull/243
[#246]: https://github.com/planetarium/libplanet/pull/246
[#247]: https://github.com/planetarium/libplanet/pull/247
[#251]: https://github.com/planetarium/libplanet/pull/251
[#256]: https://github.com/planetarium/libplanet/pull/256


Version 0.2.2
-------------

Released on April 12, 2019.

 -  Fixed a bug that `BlockChain<T>.GetStates()` had returned slower than
    necessary for many addresses.  [[#189], [#192]]

[#189]: https://github.com/planetarium/libplanet/issues/189
[#192]: https://github.com/planetarium/libplanet/pull/192


Version 0.2.1
-------------

Released on April 7, 2019.

This version purposes to entirely replace *0.2.0*, because a wrong *.nupkg*
file was uploaded to *0.2.0* on NuGet Gallery.  Note that *0.2.0* on NuGet
Gallery was unlisted.


Version 0.2.0
-------------

Released on April 5, 2019.

 -  `PrivateKey.Decrypt()` now throws an `InvalidCiphertextException`
    instead of returning `null` when `cipherText` is invalid.  [[#140]]
 -  `Transaction<T>`'s `Sender`–`Recipient` model was replaced by
    `Signer`–`UpdatedAddresses` model.   Unlike cryptocurrencies,
    transactions in games are not necessarily a transfer of assets,
    so it is difficult to determine what type of assert is transferred
    or who will receives the asset.  A more useful perspective is,
    like what kind of transformation is performed, or what states
    are changed.  To be close to this perspective, we decided to
    get rid of `Transaction<T>.Recipient` (which is singular) and
    have `Transaction<T>.UpdatedAddresses` (which is plural) instead.
    As there is no more asset to transfer, the term `Sender` was also
    renamed to `Signer`, which fits more to the new perspective.
    [[#121]]

     -  Renamed `Transaction<T>.Sender`, `RawTransaction.Signer`, and
        `IActionContext.From` properties to `Signer`.
        The corresponding parameter names on constructors and
        methods were also renamed too.
     -  Old `Transaction<T>.Make()` factory method is replaced by
        new `Transaction<T>.Create()` factory method.  The `timestamp` parameter
        became optional, and the new optional `updatedAddresses` parameter was
        added.
     -  Removed `IActionContext.To` property.
     -  `Transaction<T>.Recipient` and `RawTransaction.Recipient` properties
        were replaced by `Transaction<T>.UpdatedAddresses` and
        `RawTransaction.UpdatedAddresses` properties.
        The corresponding parameter names on constructors and methods were
        replaced too.
     -  Since the schema of `RawTransaction` class was changed,
        the serialization format of transactions and blocks were also changed.
        It affects to the way to generate `Transaction<T>.Signature`,
        `Transaction<T>.Id`, and `Block.Hash` values as well.
     -  Added `InvalidTxUpdatedAddressesException` exception class.
     -  A nullary overload of `Block<T>.Validate()` method was gone
        so that the block validation API is always time-wise.
        Instead, `Block<T>.Validate()` method now has only one overload:
        `Validate(DateTimeOffset, AccountStateGetter)` returning
        `IAccountStateDelta`.
     -  `Block<T>.Validate()` and `BlockChain<T>.Validate()` methods now can
        throw an `InvalidTxUpdateAddressesException`.

 -  The `Address`es `IAction` tries to update no more need to be manually
    coded using `IAction.RequestStates()` method.  That method was
    removed at all, and updated `Address`es became automatically determined
    (for the most cases) by track "dirties" on <dfn>rehearsal mode<dfn>.
    This mode dry-runs `IAction`s with empty `IActionContext.PreviousStates`.
    [[#121]]

     -  Added `AccountStateGetter` delegate to provide a read-only view to
        account states.
     -  Added `IAccountStateDelta` interface to replace `AddressStateMap`.
        The interface purposes to provide a read-write view to account states
        with maintaining `UpdatedAddresses` (so-called "dirty").
        [[#98]]
     -  The type of `IActionContext.PreviousStates` property was changed from
        `AddressStateMap` to `IAccountStateDelta`.
     -  Added `IActionContext.Rehearsal` property.  [[#131], [#135]]
     -  Added `UnexpectedlyTerminatedTxRehearsalException` class.
        [[#132], [#136]]
     -  The return type of `IAction.Execute()` method was changed from
        `AddressStateMap` to `IAccountStateDelta`.
     -  Removed `IAction.RequestStates()` method because there is no need for it
        and thus it is not used anymore.
     -  Added `Transaction<T>.EvaluateActions()` method.
     -  Added `Block<T>.EvaluateActions()` generator method.

 -  The built-in subtype polymorphism of `IAction` and `Transaction<T>` was
    moved to a separated new `PolymorphicAction<T>` abstract class.
    Polymorphic actions now should be wrapped by `PolymorphicAction<T>`.
    For example, the following code:

    ~~~~ csharp
    public abstract class AbstractAction : IAction { ... }

    [ActionType("attack")]
    public sealed class Attack : AbstractAction { ... }

    [ActionType("sleep")]
    public sealed class Sleep : AbstractAction { ... }
    ~~~~

    ~~~~ csharp
    var tx = Transaction<AbstractAction>.Create(
        ...,
        actions: new[] { new Attack(...), ... }
    );
    ~~~~

    should be changed to like:

    ~~~~ csharp
    var tx = Transaction<PolymorphicAction<AbstractAction>>.Create(
        ...,
        actions: new[] {
            new PolymorphicAction<AbstractAction>(new Attack(...)),
            ...
        }
    );
    ~~~~

    It can be simpler by implicit casting:

    ~~~~ csharp
    var tx = Transaction<PolymorphicAction<AbstractAction>>.Create(
        ...,
        actions: new PolymorphicAction<AbstractAction>[] { new Attack(...), }
    );
    ~~~~

    [[#169]]

     -  The type parameter `T` of `Transaction<T>`, `Block<T>`, and
        `BlockChain<T>` became to require having a `public` parameterless
        constructor (i.e., `new()`) besides implementing `IAction` interface.
        This means an `abstract class` or an `interface` no more can be passed
        to `T`, but only a concrete `class` or a `struct` can be passed.

 -  Fixed a bug that mutating a collection of `IAction`s passed to
    constructors or factory methods of `Transaction<T>` had affected
    made instances as well.
    The type of `Transaction<T>.Actions` property was changed from
    `IList<T>` to `IImmutableList<T>`.  The corresponding parameters on
    constructors and factory methods also were changed to take
    `IEnumerable<T>` instead of `IList<T>`.
 -  `Address` and `TxId` are now serializable.
    [[#99], [#124] by Qria]
 -  `InvalidTxException` and its subclasses became to have `TxId` property
    and the corresponding constructor parameter.  This can be useful when
    multiple `Transaction<T>` objects are validated at once.
 -  Added `Address.Size` constant, which is fixed to the `Int32` 20.
 -  Fixed a bug that `Block<T>.Validate()` had not thrown `InvalidTxException`
    even if there is any integrity error on its `Transactions`.
 -  Improved the write throughput of `BlockChain<T>` while polling
    `BlockChain<T>.GetStates()`
 -  `Swarm.AddPeersAsync()` was fixed so that unreachable `Peer`s are ignored.
    [[#128]]
 -  `Swarm` became able to relay their connection via TURN ([RFC 5766])
    to NAT traversal. To enable this, its constructor (`Swarm()`) takes the
    newly added `IceServer`s as configuration.
 -  Since we decided to depend on TURN ([RFC 5766]) and STUN ([RFC 5389]) to
    work around NAT so that `Peer`'s endpoints don't have to be multiple,
    `Peer.Urls` was renamed to `Peer.EndPoint` and its type also was changed
    from `IImmutableList<Uri>` to `DnsEndPoint`.
    [[#120], [#123] by Yang Chun Ung, [#126], [#127], [#165], [#166]]
 -  `Swarm` became to ignore tip blocks of the same height (`Index`) that it
    already has and deal with only longer (higher) blocks.
 -  Fixed a bug that occurred when `Swarm` was handling multiple responses at
    the same time.
 -  Fixed a bug that the `Swarm` constructor had hanged in certain runtimes
    like Unity engine.
 -  Removed `AddressTransactionSet` which handles handle `Address` to
    `IEnumerable<TxId>` indices, and the following methods in `IStore`:
     -  `IStore.IterateAddresses()`
     -  `IStore.GetAddressTransactionIds()`
     -  `IStore.AppendAddressTransactionId()`
     -  `IStore.CountAddresses()`
 -  Added `IStore.ListNamespaces()` method.
 -  `IStore.CountBlocks()` and `IStore.CountTransactions()` became to return
    `long`.
 -  Block/tx-related methods in `IStore` and `BaseIndex<T>` no longer
    accepts `@namespace` parameter.  It means that even if a forking occurs, the
    same block/tx files are shared.
 -  Fixed a bug that made unnecessary fork when receiving blocks from other
    peer.
 -  Action classes that implement `IAction` but lack `ActionTypeAttribute`
    became reported by `PolymorphicAction<T>` throwing
    `MissingActionTypeException` at runtime.  [[#28], [#144], [#169]]
 -  Turn into parameter in `BlockPolicy`'s constructor to milliseconds. [[#151]]
 -  `BencodexFormatter` became able to serialize `BigInteger`.  [[#159]]
 -  Made `Swarm` possible to configure its network `appProtocolVersion` and,
    to ignore peers if their version is different.  [[#167]], [[#170]]
 -  Added `DifferentAppProtocolVersionException` class.  [[#167], [#170]]
 -  Added `IActionContext.Miner` property.  [[#173]], [[#174]]
 -  Renamed `Block<T>.RewardBeneficiary` to `Block<T>.Miner`.  [[#174]]
 -  Added `BlockChain<T>.Blocks` property.  [[#176]]
 -  Added `BlockChain<T>.Transactions` property.  [[#176]]

[#28]: https://github.com/planetarium/libplanet/issues/28
[#98]: https://github.com/planetarium/libplanet/issues/98
[#99]: https://github.com/planetarium/libplanet/issues/99
[#120]: https://github.com/planetarium/libplanet/issues/120
[#121]: https://github.com/planetarium/libplanet/pull/121
[#123]: https://github.com/planetarium/libplanet/pull/123
[#124]: https://github.com/planetarium/libplanet/pull/124
[#126]: https://github.com/planetarium/libplanet/issues/126
[#127]: https://github.com/planetarium/libplanet/pull/127
[#128]: https://github.com/planetarium/libplanet/pull/128
[#131]: https://github.com/planetarium/libplanet/issues/131
[#132]: https://github.com/planetarium/libplanet/issues/132
[#135]: https://github.com/planetarium/libplanet/pull/135
[#136]: https://github.com/planetarium/libplanet/pull/136
[#140]: https://github.com/planetarium/libplanet/pull/140
[#144]: https://github.com/planetarium/libplanet/pull/144
[#151]: https://github.com/planetarium/libplanet/pull/151
[#159]: https://github.com/planetarium/libplanet/pull/159
[#165]: https://github.com/planetarium/libplanet/issues/165
[#166]: https://github.com/planetarium/libplanet/pull/166
[#167]: https://github.com/planetarium/libplanet/issues/167
[#169]: https://github.com/planetarium/libplanet/pull/169
[#170]: https://github.com/planetarium/libplanet/pull/170
[#173]: https://github.com/planetarium/libplanet/issues/173
[#174]: https://github.com/planetarium/libplanet/pull/174
[#176]: https://github.com/planetarium/libplanet/pull/176
[RFC 5389]: https://tools.ietf.org/html/rfc5389
[RFC 5766]: https://tools.ietf.org/html/rfc5766


Version 0.1.1
-------------

Released on March 5, 2019.

 -  Improved stability of `Swarm` and `SwarmTest`.


Version 0.1.0
-------------

Initial release.  Released on February 26, 2019.
