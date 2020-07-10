// @flow strict-local

import type {AbortSignal} from 'abortcontroller-polyfill/dist/cjs-ponyfill';
import type {FilePath, ModuleSpecifier, Symbol} from '@parcel/types';
import type WorkerFarm, {Handle} from '@parcel/workers';
import type {Event} from '@parcel/watcher';
import type {
  Asset,
  AssetGraphNode,
  AssetGroup,
  AssetNode,
  AssetRequestInput,
  Dependency,
  DependencyNode,
  Entry,
  ParcelOptions,
  ValidationOpts,
} from './types';
import type {ConfigAndCachePath} from './requests/ParcelConfigRequest';
import type {EntryResult} from './requests/EntryRequest';
import type {TargetResolveResult} from './requests/TargetRequest';

import EventEmitter from 'events';
import invariant from 'assert';
import nullthrows from 'nullthrows';
import path from 'path';
import {md5FromObject, md5FromString, PromiseQueue} from '@parcel/utils';
import AssetGraph from './AssetGraph';
import RequestTracker, {RequestGraph} from './RequestTracker';
import {PARCEL_VERSION} from './constants';
import ParcelConfig from './ParcelConfig';

import createParcelConfigRequest from './requests/ParcelConfigRequest';
import createEntryRequest from './requests/EntryRequest';
import createTargetRequest from './requests/TargetRequest';
import createAssetRequest from './requests/AssetRequest';
import createPathRequest from './requests/PathRequest';

import Validation from './Validation';
import {report} from './ReporterRunner';

import dumpToGraphViz from './dumpGraphToGraphViz';

type Opts = {|
  options: ParcelOptions,
  optionsRef: number,
  name: string,
  entries?: Array<string>,
  assetGroups?: Array<AssetGroup>,
  workerFarm: WorkerFarm,
|};

const typesWithRequests = new Set([
  'entry_specifier',
  'entry_file',
  'dependency',
  'asset_group',
]);

export default class AssetGraphBuilder extends EventEmitter {
  assetGraph: AssetGraph;
  requestGraph: RequestGraph;
  requestTracker: RequestTracker;
  assetRequests: Array<AssetGroup>;
  runValidate: ValidationOpts => Promise<void>;
  queue: PromiseQueue<mixed>;

  changedAssets: Map<string, Asset> = new Map();
  options: ParcelOptions;
  optionsRef: number;
  workerFarm: WorkerFarm;
  cacheKey: string;
  entries: ?Array<string>;
  initialAssetGroups: ?Array<AssetGroup>;

  handle: Handle;

  async init({
    options,
    optionsRef,
    entries,
    name,
    assetGroups,
    workerFarm,
  }: Opts) {
    this.options = options;
    this.optionsRef = optionsRef;
    this.entries = entries;
    this.initialAssetGroups = assetGroups;
    this.workerFarm = workerFarm;
    this.assetRequests = [];

    // TODO: changing these should not throw away the entire graph.
    // We just need to re-run target resolution.
    let {hot, publicUrl, distDir, minify, scopeHoist} = options;
    this.cacheKey = md5FromObject({
      parcelVersion: PARCEL_VERSION,
      name,
      options: {hot, publicUrl, distDir, minify, scopeHoist},
      entries,
    });

    this.queue = new PromiseQueue();

    this.runValidate = workerFarm.createHandle('runValidate');

    let changes = await this.readFromCache();
    if (!changes) {
      this.assetGraph = new AssetGraph();
      this.requestGraph = new RequestGraph();
    }

    this.assetGraph.initOptions({
      onNodeRemoved: node => this.handleNodeRemovedFromAssetGraph(node),
    });

    this.requestTracker = new RequestTracker({
      graph: this.requestGraph,
      farm: workerFarm,
      options: this.options,
    });

    if (changes) {
      this.requestGraph.invalidateUnpredictableNodes();
      this.requestTracker.respondToFSEvents(changes);
    } else {
      this.assetGraph.initialize({
        entries,
        assetGroups,
      });
    }
  }

  async build(
    signal?: AbortSignal,
  ): Promise<{|
    assetGraph: AssetGraph,
    changedAssets: Map<string, Asset>,
  |}> {
    this.requestTracker.setSignal(signal);

    let errors = [];

    let root = this.assetGraph.getRootNode();
    if (!root) {
      throw new Error('A root node is required to traverse');
    }

    let visited = new Set([root.id]);
    const visit = (node: AssetGraphNode) => {
      if (errors.length > 0) {
        return;
      }

      if (this.shouldSkipRequest(node)) {
        visitChildren(node);
      } else {
        this.queueCorrespondingRequest(node).then(
          () => visitChildren(node),
          error => errors.push(error),
        );
      }
    };
    const visitChildren = (node: AssetGraphNode) => {
      for (let child of this.assetGraph.getNodesConnectedFrom(node)) {
        if (
          (!visited.has(child.id) || child.hasDeferred) &&
          this.assetGraph.shouldVisitChild(node, child)
        ) {
          visited.add(child.id);
          visit(child);
        }
      }
    };
    visit(root);

    await this.queue.run();

    if (errors.length) {
      throw errors[0]; // TODO: eventually support multiple errors since requests could reject in parallel
    }

    this.topologicalBfs((assetNode, incomingDeps, outgoingDeps) => {
      let hasDirtyOutgoingDep = false;

      // exportSymbol -> identifier
      let assetSymbols = assetNode.value.symbols;
      // identifier -> exportSymbol
      let assetSymbolsInverse = assetNode.value.symbols
        ? new Map(
            [...assetNode.value.symbols].map(([key, val]) => [val.local, key]),
          )
        : null;

      let hasNamespaceOutgoingDeps = outgoingDeps.some(
        d => d.value.symbols?.get('*')?.local === '*',
      );

      // 1) Determine what the incomingDeps requests from the asset
      // ----------------------------------------------------------

      let isEntry = false;

      // Used symbols that are exported or reexported (symbol will be removed again later) by asset.
      assetNode.usedSymbols = new Set();

      // Symbols that have to be namespace reexported by outgoingDeps.
      let namespaceReexportedSymbols = new Set<Symbol>();

      if (incomingDeps.length === 0) {
        // Root in the runtimes Graph
        assetNode.usedSymbols.add('*');
        namespaceReexportedSymbols.add('*');
      } else {
        for (let incomingDep of incomingDeps) {
          if (incomingDep.value.symbols == null) {
            isEntry = true;
            continue;
          }

          for (let exportSymbol of incomingDep.usedSymbolsDown) {
            if (exportSymbol === '*') {
              assetNode.usedSymbols.add('*');
              namespaceReexportedSymbols.add('*');
            }
            if (
              !assetSymbols ||
              assetSymbols.has(exportSymbol) ||
              assetSymbols.has('*')
            ) {
              // An own symbol or a non-namespace reexport
              assetNode.usedSymbols.add(exportSymbol);
            }
            // A namespace reexport
            // (but only if we actually have namespace-exporting outgoing dependencies,
            // This usually happens with a reexporting asset with many namespace exports which means that
            // we cannot match up the correct asset with the used symbol at this level.)
            else if (hasNamespaceOutgoingDeps) {
              namespaceReexportedSymbols.add(exportSymbol);
            }
          }
        }
      }

      // console.log(1, {
      //   asset: assetNode.value.filePath,
      //   used: assetNode.usedSymbols,
      //   namespaceReexportedSymbols,
      //   incomingDeps: incomingDeps.map(d => [
      //     d.value.moduleSpecifier,
      //     ...d.usedSymbolsDown,
      //   ]),
      // });

      // 2) Distribute the symbols to the outgoing dependencies
      // ----------------------------------------------------------

      for (let dep of outgoingDeps) {
        let depUsedSymbolsDownOld = dep.usedSymbolsDown;
        dep.usedSymbolsDown = new Set();
        if (
          // For entries, we still need to add dep.value.symbols of the entry (which are "used" but not according to the symbols data)
          isEntry ||
          // If not a single asset is used, we can say the entire subgraph is not used.
          // This is e.g. needed when some symbol is imported and then used for a export which isn't used (= "semi-weak" reexport)
          //    index.js:     `import {bar} from "./lib"; ...`
          //    lib/index.js: `export * from "./foo.js"; export * from "./bar.js";`
          //    lib/foo.js:   `import { data } from "./bar.js"; export const foo = data + " esm2";`
          // TODO is this really valid?
          assetNode.usedSymbols.size > 0 ||
          namespaceReexportedSymbols.size > 0
        ) {
          let depSymbols = dep.value.symbols;
          if (!depSymbols) continue;

          if (depSymbols.get('*')?.local === '*') {
            for (let s of namespaceReexportedSymbols) {
              // We need to propagate the namespaceReexportedSymbols to all namespace dependencies (= even wrong ones because we don't know yet)
              dep.usedSymbolsDown.add(s);
            }
          }

          for (let [symbol, {local}] of depSymbols) {
            // Was already handled above
            if (local === '*') continue;

            if (!assetSymbolsInverse || !depSymbols.get(symbol)?.isWeak) {
              // Bailout or non-weak symbol (= used in the asset itself = not a reexport)
              dep.usedSymbolsDown.add(symbol);
            } else {
              let reexportedExportSymbol = assetSymbolsInverse.get(local);
              if (
                reexportedExportSymbol == null // not reexported = used in asset itself
              ) {
                dep.usedSymbolsDown.add(symbol);
              } else if (
                assetNode.usedSymbols.has('*') || // we need everything
                assetNode.usedSymbols.has(reexportedExportSymbol) // reexported
              ) {
                // The symbol is indeed a reexport, so it's not used from the asset itself
                dep.usedSymbolsDown.add(symbol);

                assetNode.usedSymbols.delete(reexportedExportSymbol);
              }
            }
          }

          if (!equalSet(depUsedSymbolsDownOld, dep.usedSymbolsDown))
            hasDirtyOutgoingDep = true;
        }

        // console.log(2, {
        //   from: assetNode.value.filePath,
        //   to: dep.value.moduleSpecifier,
        //   dirty: dep.usedSymbolsDownDirty,
        //   old: [...depUsedSymbolsDownOld]
        //     .filter(([, v]) => v.size > 0)
        //     .map(([k, v]) => [k, ...v]),
        //   new: [...dep.usedSymbolsDown]
        //     .filter(([, v]) => v.size > 0)
        //     .map(([k, v]) => [k, ...v]),
        // });
      }

      return hasDirtyOutgoingDep;
    });

    this.dfsPostorder((node, incomingDeps, outgoingDeps) => {
      let assetSymbols = node.value.symbols;

      if (!assetSymbols) {
        for (let dep of incomingDeps) {
          dep.usedSymbolsUp = new Set(node.usedSymbols);
        }
      } else {
        let assetSymbolsInverse = new Map(
          [...assetSymbols].map(([key, val]) => [val.local, key]),
        );

        let reexportedSymbols = new Set<string>();
        for (let outgoingDep of outgoingDeps) {
          let outgoingDepSymbols = outgoingDep.value.symbols;
          if (!outgoingDepSymbols) continue;

          if (outgoingDepSymbols.get('*')?.local === '*') {
            outgoingDep.usedSymbolsUp.forEach(s => reexportedSymbols.add(s));
          } else {
            for (let s of outgoingDep.usedSymbolsUp) {
              if (!outgoingDep.usedSymbolsDown.has(s)) {
                // usedSymbolsDown is a superset of usedSymbolsUp
                continue;
              }

              let reexported = assetSymbolsInverse.get(
                nullthrows(outgoingDepSymbols.get(s), s).local,
              );
              if (reexported != null) {
                reexportedSymbols.add(reexported);
              }
            }
          }
        }

        for (let incomingDep of incomingDeps) {
          incomingDep.usedSymbolsUp = new Set();
          for (let s of incomingDep.usedSymbolsDown) {
            if (
              node.usedSymbols.has(s) ||
              reexportedSymbols.has(s) ||
              s === '*'
            ) {
              incomingDep.usedSymbolsUp.add(s);
            }
          }
        }
      }
    });

    dumpToGraphViz(this.assetGraph, 'AssetGraph');
    // $FlowFixMe Added in Flow 0.121.0 upgrade in #4381
    dumpToGraphViz(this.requestGraph, 'RequestGraph');

    let changedAssets = this.changedAssets;
    this.changedAssets = new Map();
    return {assetGraph: this.assetGraph, changedAssets: changedAssets};
  }

  topologicalBfs(
    visit: (
      node: AssetNode,
      incoming: $ReadOnlyArray<DependencyNode>,
      outgoing: $ReadOnlyArray<DependencyNode>,
    ) => boolean,
  ) {
    let root = this.assetGraph.getRootNode();
    if (!root) {
      throw new Error('A root node is required to traverse');
    }

    let queue: Array<AssetGraphNode> = [root];
    let visited = new Set<AssetGraphNode>([root]);
    let skipped = new Set<AssetGraphNode>();

    while (queue.length > 0) {
      let node = queue.shift();
      let outgoing = this.assetGraph.getNodesConnectedFrom(node);
      if (
        node.type !== 'dependency' &&
        this.assetGraph.getNodesConnectedTo(node).some(d => !visited.has(d))
      ) {
        // only visit node once all parents were visited, it will be visited again later by the last parent
        skipped.add(node);
      } else {
        if (node.type === 'asset') {
          visit(
            node,
            this.assetGraph.getIncomingDependencies(node.value).map(d => {
              let dep = this.assetGraph.getNode(d.id);
              invariant(dep && dep.type === 'dependency');
              return dep;
            }),
            outgoing.map(dep => {
              invariant(dep.type === 'dependency');
              return dep;
            }),
          );
        }

        visited.add(node);
        skipped.delete(node);
        for (let child of outgoing) {
          if (!visited.has(child)) {
            queue.push(child);
          }
        }
      }
    }

    // circular dependencies
    queue = [...skipped];
    let dirty = new Set();
    while (queue.length > 0) {
      let node = queue.shift();
      let outgoing = this.assetGraph.getNodesConnectedFrom(node);
      let hasDirtyOutgoingDep = false;
      if (node.type === 'asset') {
        hasDirtyOutgoingDep = visit(
          node,
          this.assetGraph.getIncomingDependencies(node.value).map(d => {
            let dep = this.assetGraph.getNode(d.id);
            invariant(dep && dep.type === 'dependency');
            return dep;
          }),
          outgoing.map(dep => {
            invariant(dep.type === 'dependency');
            return dep;
          }),
        );
      }

      visited.add(node);
      let forceVisitChildren =
        (node.type !== 'asset' && dirty.has(node)) || hasDirtyOutgoingDep;
      for (let child of outgoing) {
        if (forceVisitChildren) dirty.add(child);
        if (forceVisitChildren || !visited.has(child)) {
          queue.push(child);
        }
      }
      dirty.delete(node);
    }
  }

  dfsPostorder(
    visit: (
      node: AssetNode,
      incoming: $ReadOnlyArray<DependencyNode>,
      outgoing: $ReadOnlyArray<DependencyNode>,
    ) => void,
  ) {
    let root = this.assetGraph.getRootNode();
    if (!root) {
      throw new Error('A root node is required to traverse');
    }

    let visited = new Set([root.id]);
    const walk = (node: AssetGraphNode) => {
      let outgoing = this.assetGraph.getNodesConnectedFrom(node);
      for (let child of this.assetGraph.getNodesConnectedFrom(node)) {
        if (!visited.has(child.id)) {
          visited.add(child.id);
          walk(child);
        }
      }
      if (node.type === 'asset') {
        visit(
          node,
          this.assetGraph.getIncomingDependencies(node.value).map(d => {
            let n = this.assetGraph.getNode(d.id);
            invariant(n && n.type === 'dependency');
            return n;
          }),
          outgoing.map(dep => {
            invariant(dep.type === 'dependency');
            return dep;
          }),
        );
      }
    };
    walk(root);
  }

  // TODO: turn validation into a request
  async validate(): Promise<void> {
    let {config: processedConfig, cachePath} = nullthrows(
      await this.requestTracker.runRequest<null, ConfigAndCachePath>(
        createParcelConfigRequest(),
      ),
    );

    let config = new ParcelConfig(
      processedConfig,
      this.options.packageManager,
      this.options.autoinstall,
    );
    let trackedRequestsDesc = this.assetRequests.filter(request => {
      return config.getValidatorNames(request.filePath).length > 0;
    });

    // Schedule validations on workers for all plugins that implement the one-asset-at-a-time "validate" method.
    let promises = trackedRequestsDesc.map(request =>
      this.runValidate({
        requests: [request],
        optionsRef: this.optionsRef,
        configCachePath: cachePath,
      }),
    );

    // Skip sending validation requests if no validators were configured
    if (trackedRequestsDesc.length === 0) {
      return;
    }

    // Schedule validations on the main thread for all validation plugins that implement "validateAll".
    promises.push(
      new Validation({
        requests: trackedRequestsDesc,
        options: this.options,
        config,
        report,
        dedicatedThread: true,
      }).run(),
    );

    this.assetRequests = [];
    await Promise.all(promises);
  }

  shouldSkipRequest(node: AssetGraphNode) {
    return (
      node.complete === true ||
      !typesWithRequests.has(node.type) ||
      (node.correspondingRequest != null &&
        this.requestGraph.getNode(node.correspondingRequest) != null &&
        this.requestTracker.hasValidResult(node.correspondingRequest))
    );
  }

  queueCorrespondingRequest(node: AssetGraphNode) {
    switch (node.type) {
      case 'entry_specifier':
        return this.queue.add(() => this.runEntryRequest(node.value));
      case 'entry_file':
        return this.queue.add(() => this.runTargetRequest(node.value));
      case 'dependency':
        return this.queue.add(() => this.runPathRequest(node.value));
      case 'asset_group':
        return this.queue.add(() => this.runAssetRequest(node.value));
      default:
        throw new Error(
          `Can not queue corresponding request of node with type ${node.type}`,
        );
    }
  }

  async runEntryRequest(input: ModuleSpecifier) {
    let request = createEntryRequest(input);
    let result = await this.requestTracker.runRequest<FilePath, EntryResult>(
      request,
    );
    this.assetGraph.resolveEntry(request.input, result.entries, request.id);
  }

  async runTargetRequest(input: Entry) {
    let request = createTargetRequest(input);
    let result = await this.requestTracker.runRequest<
      Entry,
      TargetResolveResult,
    >(request);
    this.assetGraph.resolveTargets(request.input, result.targets, request.id);
  }

  async runPathRequest(input: Dependency) {
    let request = createPathRequest(input);
    let result = await this.requestTracker.runRequest<Dependency, ?AssetGroup>(
      request,
    );
    this.assetGraph.resolveDependency(input, result, request.id);
  }

  async runAssetRequest(input: AssetGroup) {
    this.assetRequests.push(input);
    let request = createAssetRequest({
      ...input,
      optionsRef: this.optionsRef,
    });
    let assets = await this.requestTracker.runRequest<
      AssetRequestInput,
      Array<Asset>,
    >(request);

    if (assets != null) {
      for (let asset of assets) {
        this.changedAssets.set(asset.id, asset);
      }
      this.assetGraph.resolveAssetGroup(input, assets, request.id);
    }
  }

  handleNodeRemovedFromAssetGraph(node: AssetGraphNode) {
    if (node.correspondingRequest != null) {
      this.requestTracker.removeRequest(node.correspondingRequest);
    }
  }

  respondToFSEvents(events: Array<Event>) {
    return this.requestGraph.respondToFSEvents(events);
  }

  getWatcherOptions() {
    let vcsDirs = ['.git', '.hg'].map(dir =>
      path.join(this.options.projectRoot, dir),
    );
    let ignore = [this.options.cacheDir, ...vcsDirs];
    return {ignore};
  }

  getCacheKeys() {
    let assetGraphKey = md5FromString(`${this.cacheKey}:assetGraph`);
    let requestGraphKey = md5FromString(`${this.cacheKey}:requestGraph`);
    let snapshotKey = md5FromString(`${this.cacheKey}:snapshot`);
    return {assetGraphKey, requestGraphKey, snapshotKey};
  }

  async readFromCache(): Promise<?Array<Event>> {
    if (this.options.disableCache) {
      return null;
    }

    let {assetGraphKey, requestGraphKey, snapshotKey} = this.getCacheKeys();
    let assetGraph = await this.options.cache.get(assetGraphKey);
    let requestGraph = await this.options.cache.get(requestGraphKey);

    if (assetGraph && requestGraph) {
      this.assetGraph = assetGraph;
      this.requestGraph = requestGraph;

      let opts = this.getWatcherOptions();
      let snapshotPath = this.options.cache._getCachePath(snapshotKey, '.txt');
      return this.options.inputFS.getEventsSince(
        this.options.projectRoot,
        snapshotPath,
        opts,
      );
    }

    return null;
  }

  async writeToCache() {
    if (this.options.disableCache) {
      return;
    }

    let {assetGraphKey, requestGraphKey, snapshotKey} = this.getCacheKeys();
    await this.options.cache.set(assetGraphKey, this.assetGraph);
    await this.options.cache.set(requestGraphKey, this.requestGraph);

    let opts = this.getWatcherOptions();
    let snapshotPath = this.options.cache._getCachePath(snapshotKey, '.txt');
    await this.options.inputFS.writeSnapshot(
      this.options.projectRoot,
      snapshotPath,
      opts,
    );
  }
}

function equalSet<T>(a: $ReadOnlySet<T>, b: $ReadOnlySet<T>) {
  return a.size === b.size && [...a].every(i => b.has(i));
}
