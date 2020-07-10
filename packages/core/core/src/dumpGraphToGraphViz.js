// @flow

import type {Environment} from './types';

import type Graph from './Graph';
import type {AssetGraphNode, BundleGraphNode} from './types';

import path from 'path';

const COLORS = {
  root: 'gray',
  asset: 'green',
  dependency: 'orange',
  transformer_request: 'cyan',
  file: 'gray',
  default: 'white',
};

const TYPE_COLORS = {
  bundle: 'blue',
  contains: 'grey',
  internal_async: 'orange',
  references: 'red',
};

export default async function dumpGraphToGraphViz(
  // $FlowFixMe
  graph: Graph<AssetGraphNode> | Graph<BundleGraphNode>,
  name: string,
): Promise<void> {
  if (
    process.env.PARCEL_BUILD_ENV === 'production' ||
    process.env.PARCEL_DUMP_GRAPHVIZ == null ||
    // $FlowFixMe
    process.env.PARCEL_DUMP_GRAPHVIZ == false
  ) {
    return;
  }
  let detailedSymbols = process.env.PARCEL_DUMP_GRAPHVIZ === 'symbols';

  const graphviz = require('graphviz');
  const tempy = require('tempy');
  let g = graphviz.digraph('G');
  let nodes = Array.from(graph.nodes.values());
  for (let node of nodes) {
    let n = g.addNode(node.id);
    // $FlowFixMe default is fine. Not every type needs to be in the map.
    n.set('color', COLORS[node.type || 'default']);
    n.set('shape', 'box');
    n.set('style', 'filled');
    let label = `${node.type || 'No Type'}: [${node.id}]: `;
    if (node.type === 'dependency') {
      label += node.value.moduleSpecifier;
      let parts = [];
      if (node.value.isEntry) parts.push('entry');
      if (node.value.isAsync) parts.push('async');
      if (node.value.isOptional) parts.push('optional');
      if (node.value.isIsolated) parts.push('isolated');
      if (node.value.isURL) parts.push('url');
      if (node.deferred) parts.push('deferred');
      if (parts.length) label += ' (' + parts.join(', ') + ')';
      if (node.value.env) label += ` (${getEnvDescription(node.value.env)})`;
      if (detailedSymbols) {
        if (node.value.symbols.size) {
          label +=
            '\nsymbols: ' +
            [...node.value.symbols].map(([e, {local}]) => [e, local]).join(';');
        }
        let weakSymbols = [...node.value.symbols]
          .filter(([, {isWeak}]) => isWeak)
          .map(([s]) => s);
        if (weakSymbols.length) {
          label += '\nweakSymbols: ' + weakSymbols.join(',');
        }
        let usedSymbolsDown = [...node.usedSymbolsDown]
          .filter(([, v]) => v.size > 0)
          .map(([v]) => v);
        if (usedSymbolsDown.length) {
          label += '\nusedSymbolsDown: ' + usedSymbolsDown.join(',');
        }
        if (node.usedSymbolsUp.size) {
          label += '\nusedSymbolsUp: ' + [...node.usedSymbolsUp].join(',');
        }
        if (node.usedSymbolsDownDirty) parts.push('\nusedSymbolsDirty');
      }
    } else if (node.type === 'asset') {
      label += path.basename(node.value.filePath) + '#' + node.value.type;
      if (detailedSymbols) {
        if (node.value.symbols) {
          if (node.value.symbols.size)
            label +=
              '\nsymbols: ' +
              [...node.value.symbols]
                .map(([e, {local}]) => [e, local])
                .join(';');
        } else {
          label += '\nsymbols: cleared';
        }
        let usedSymbols = [...node.usedSymbols]
          .filter(([, v]) => v.size > 0)
          .map(([v]) => v);
        if (usedSymbols.length) {
          label += '\nusedSymbols: ' + usedSymbols.join(',');
        }
      }
    } else if (node.type === 'file') {
      label += path.basename(node.value.filePath);
    } else if (node.type === 'transformer_request') {
      label +=
        path.basename(node.value.filePath) +
        ` (${getEnvDescription(node.value.env)})`;
    } else if (node.type === 'bundle') {
      let parts = [];
      if (node.value.isEntry) parts.push('entry');
      if (node.value.isInline) parts.push('inline');
      if (parts.length) label += ' (' + parts.join(', ') + ')';
      if (node.value.env) label += ` (${getEnvDescription(node.value.env)})`;
    } else if (node.type === 'request') {
      label = node.value.type + ':' + node.id;
    }
    n.set('label', label);
  }
  for (let edge of graph.getAllEdges()) {
    let gEdge = g.addEdge(edge.from, edge.to);
    let color = edge.type != null ? TYPE_COLORS[edge.type] : null;
    if (color != null) {
      gEdge.set('color', color);
    }
  }
  let tmp = tempy.file({name: `${name}.png`});
  await g.output('png', tmp);
  // eslint-disable-next-line no-console
  console.log('Dumped', tmp);
}

function getEnvDescription(env: Environment) {
  let description;
  if (typeof env.engines.browsers === 'string') {
    description = `${env.context}: ${env.engines.browsers}`;
  } else if (Array.isArray(env.engines.browsers)) {
    description = `${env.context}: ${env.engines.browsers.join(', ')}`;
  } else if (env.engines.node) {
    description = `node: ${env.engines.node}`;
  }

  return description ?? '';
}
