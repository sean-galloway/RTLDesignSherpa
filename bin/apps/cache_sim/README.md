# Cache Associativity Simulator

A standalone, trace-driven cache simulator for exploring set count, way count,
block size, and replacement policy.  Written in vanilla HTML5/CSS/ES5-ish
JavaScript with no build step; open `index.html` directly as `file://`.

## Files

```
bin/apps/cache_sim/
  index.html          -- UI
  style.css           -- mobile-first styles
  js/model.js         -- pure simulation model (no DOM)
  js/app.js           -- DOM glue, generators, and guided example
  test/run_tests.js   -- zero-dependency TAP-ish node test runner
  README.md           -- this file
```

## Model API

```js
var CACHESIM = require('./js/model.js');

var result = CACHESIM.simulate(
  { sets: 4, ways: 1, blockSize: 1, policy: 'LRU' },
  [0x00, 0x10, 0x20, 0x00],
  1   // seed for RANDOM policy / reproducibility
);
```

`simulate(config, addresses, seed)` returns:

```js
{
  config: { sets, ways, blockSize, policy },
  perAccess: [
    { addr, hit, setIndex, way, missClass }, ...
  ],
  totals: {
    hits, misses, hitRate,
    compulsory, capacity, conflict
  },
  occupancy: [ [tagOrNull, ...], ... ]   // sets x ways
}
```

`missClass` is one of `'hit'`, `'compulsory'`, `'capacity'`, or `'conflict'`.
Capacity classification is computed by running a shadow fully-associative
cache with the same total size and policy.

Other model helpers:

- `CACHESIM.validateConfig(config)` -> `{ok, errors}`
- `CACHESIM.parseAddressText(text)` -> address array (NaN for bad lines)
- `CACHESIM.generateSequential(length, start)`
- `CACHESIM.generateStrided(length, start, stride)`
- `CACHESIM.generateRandom(length, seed, maxAddr)` (default maxAddr = 256)

## Running tests

```bash
node bin/apps/cache_sim/test/run_tests.js
```

Exit code is 0 when all tests pass.

## UI features

- Sliders for sets, ways, and block size; dropdown for policy.
- Address trace textarea plus one-click sequential, strided, and random
  generators.
- Big-number hit rate, totals table, per-access log, and per-set occupancy.
- Guided example button that loads a cyclic trace and compares direct-mapped
  vs 2-way set-associative behavior.
