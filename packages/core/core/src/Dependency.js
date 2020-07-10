// @flow
import type {
  SourceLocation,
  Meta,
  ModuleSpecifier,
  Symbol,
} from '@parcel/types';
import {md5FromObject} from '@parcel/utils';
import type {Dependency, Environment, Target} from './types';
import {getEnvironmentHash} from './Environment';

type DependencyOpts = {|
  id?: string,
  sourcePath?: string,
  sourceAssetId?: string,
  moduleSpecifier: ModuleSpecifier,
  isAsync?: boolean,
  isEntry?: boolean,
  isOptional?: boolean,
  isURL?: boolean,
  isIsolated?: boolean,
  loc?: SourceLocation,
  env: Environment,
  meta?: Meta,
  target?: Target,
  symbols?: Map<
    Symbol,
    {|local: Symbol, loc: ?SourceLocation, isWeak: boolean|},
  >,
  pipeline?: ?string,
|};

export function createDependency(opts: DependencyOpts): Dependency {
  let id =
    opts.id ||
    md5FromObject({
      sourceAssetId: opts.sourceAssetId,
      moduleSpecifier: opts.moduleSpecifier,
      env: getEnvironmentHash(opts.env),
      target: opts.target,
      pipeline: opts.pipeline,
    });

  return {
    ...opts,
    id,
    isAsync: opts.isAsync ?? false,
    isEntry: opts.isEntry,
    isOptional: opts.isOptional ?? false,
    isURL: opts.isURL ?? false,
    isIsolated: opts.isIsolated ?? false,
    meta: opts.meta || {},
    symbols: opts.symbols,
  };
}

export function mergeDependencies(a: Dependency, b: Dependency): void {
  let {meta, symbols, ...other} = b;
  Object.assign(a, other);
  Object.assign(a.meta, meta);
  if (a.symbols && symbols) {
    for (let [k, v] of symbols) {
      a.symbols.set(k, v);
    }
  }
}
