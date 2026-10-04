// js/model.js -- pure cache-associativity model for cache_sim.
// Word-addressed, set/way/block configurable, with LRU/FIFO/RANDOM policies.
// Miss classification uses a shadow fully-associative cache of the same total
// size (sets=1, ways=S*W, blockSize=B).  No DOM.  Runs in the browser
// (window.CACHESIM) and under node (module.exports).
var CACHESIM = (typeof window !== 'undefined' ? window : globalThis).CACHESIM ||
               ((typeof window !== 'undefined' ? window : globalThis).CACHESIM = {});

(function (CS) {
  'use strict';

  var POLICIES = ['LRU', 'FIFO', 'RANDOM'];

  function isPowerOfTwo(x) {
    x = x >>> 0;
    return x > 0 && (x & (x - 1)) === 0;
  }

  function ilog2(x) {
    x = x >>> 0;
    var n = 0;
    while (x > 1) {
      x = x >>> 1;
      n += 1;
    }
    return n;
  }

  function numberOrSelf(x) {
    if (typeof x === 'string' && x.trim() !== '') {
      return Number(x);
    }
    return x;
  }

  function isPosInt(x) {
    return typeof x === 'number' && isFinite(x) && x === Math.floor(x) && x > 0;
  }

  // mulberry32(seed) -> { nextInt(max) }.
  // Adapted from bin/apps/ddr_drills/js/rng.js; returns integers in [0, max).
  function makeRng(seed) {
    var a = (seed >>> 0) || 1;
    function next() {
      a |= 0;
      a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    }
    return {
      nextInt: function (max) {
        return Math.floor(next() * (max >>> 0 || 1));
      }
    };
  }

  function coerceConfig(c) {
    return {
      sets: numberOrSelf(c.sets),
      ways: numberOrSelf(c.ways),
      blockSize: numberOrSelf(c.blockSize),
      policy: String(c.policy || '').toUpperCase()
    };
  }

  function validateConfig(c) {
    c = coerceConfig(c);
    var errors = {};
    if (!isPosInt(c.sets) || !isPowerOfTwo(c.sets)) {
      errors.sets = 'must be a power of two >= 1';
    }
    if (!isPosInt(c.ways)) {
      errors.ways = 'must be an integer >= 1';
    }
    if (!isPosInt(c.blockSize) || !isPowerOfTwo(c.blockSize)) {
      errors.blockSize = 'must be a power of two >= 1';
    }
    if (POLICIES.indexOf(c.policy) === -1) {
      errors.policy = 'must be LRU, FIFO, or RANDOM';
    }
    return { ok: Object.keys(errors).length === 0, errors: errors };
  }

  function parseAddressText(text) {
    var out = [];
    var lines = String(text || '').split(/\r?\n/);
    for (var i = 0; i < lines.length; i += 1) {
      var line = lines[i].replace(/\/\/.*$/, '').trim();
      if (line === '') {
        continue;
      }
      var n;
      if (line.length > 2 && line.charAt(0) === '0' &&
          (line.charAt(1) === 'x' || line.charAt(1) === 'X')) {
        n = parseInt(line, 16);
      } else {
        n = parseInt(line, 10);
      }
      if (isNaN(n)) {
        out.push(NaN);
      } else {
        out.push(n >>> 0);
      }
    }
    return out;
  }

  function validateAddresses(addresses) {
    for (var i = 0; i < addresses.length; i += 1) {
      var a = addresses[i];
      if (typeof a !== 'number' || isNaN(a) || a !== Math.floor(a) ||
          a < 0 || a > 0xFFFFFFFF) {
        return { ok: false, message: 'address ' + i + ' is not a 32-bit word address' };
      }
    }
    return { ok: true };
  }

  function generateSequential(length, start) {
    length = numberOrSelf(length);
    start = numberOrSelf(start);
    var out = [];
    for (var i = 0; i < length; i += 1) {
      out.push((start + i) >>> 0);
    }
    return out;
  }

  function generateStrided(length, start, stride) {
    length = numberOrSelf(length);
    start = numberOrSelf(start);
    stride = numberOrSelf(stride);
    var out = [];
    for (var i = 0; i < length; i += 1) {
      out.push((start + i * stride) >>> 0);
    }
    return out;
  }

  function generateRandom(length, seed, maxAddr) {
    length = numberOrSelf(length);
    seed = numberOrSelf(seed);
    maxAddr = numberOrSelf(maxAddr);
    if (!isPosInt(maxAddr)) {
      maxAddr = 256;
    }
    var rng = makeRng(seed);
    var out = [];
    for (var i = 0; i < length; i += 1) {
      out.push(rng.nextInt(maxAddr));
    }
    return out;
  }

  function moveToBack(arr, val) {
    var idx = arr.indexOf(val);
    if (idx !== -1) {
      arr.splice(idx, 1);
    }
    arr.push(val);
  }

  function Cache(config, seed) {
    this.config = config;
    this.sets = [];
    for (var i = 0; i < config.sets; i += 1) {
      var tags = [];
      for (var w = 0; w < config.ways; w += 1) {
        tags.push(null);
      }
      this.sets[i] = {
        tags: tags,
        lru: [],
        fifo: [],
        rng: config.policy === 'RANDOM' ? makeRng(seed) : null
      };
    }
  }

  Cache.prototype.access = function (addr) {
    var cfg = this.config;
    var blockAddr = addr >>> ilog2(cfg.blockSize);
    var setIndex = 0;
    var tag = blockAddr;
    if (cfg.sets !== 1) {
      var setBits = ilog2(cfg.sets);
      var mask = (Math.pow(2, setBits) - 1) >>> 0;
      setIndex = (blockAddr & mask) >>> 0;
      tag = blockAddr >>> setBits;
    }
    var set = this.sets[setIndex];
    var way = -1;
    for (var w = 0; w < cfg.ways; w += 1) {
      if (set.tags[w] !== null && set.tags[w] === tag) {
        way = w;
        break;
      }
    }
    if (way !== -1) {
      if (cfg.policy === 'LRU') {
        moveToBack(set.lru, way);
      }
      return { hit: true, setIndex: setIndex, way: way };
    }
    for (w = 0; w < cfg.ways; w += 1) {
      if (set.tags[w] === null) {
        way = w;
        break;
      }
    }
    if (way === -1) {
      if (cfg.policy === 'LRU') {
        way = set.lru.shift();
      } else if (cfg.policy === 'FIFO') {
        way = set.fifo.shift();
      } else if (cfg.policy === 'RANDOM') {
        way = set.rng.nextInt(cfg.ways);
      } else {
        way = 0;
      }
    }
    set.tags[way] = tag;
    if (cfg.policy === 'LRU') {
      moveToBack(set.lru, way);
    } else if (cfg.policy === 'FIFO') {
      set.fifo.push(way);
    }
    return { hit: false, setIndex: setIndex, way: way };
  };

  function getOccupancy(cache) {
    var occ = [];
    for (var s = 0; s < cache.config.sets; s += 1) {
      var row = [];
      for (var w = 0; w < cache.config.ways; w += 1) {
        row.push(cache.sets[s].tags[w]);
      }
      occ.push(row);
    }
    return occ;
  }

  function simulate(config, addresses, seed) {
    config = coerceConfig(config);
    var cv = validateConfig(config);
    if (!cv.ok) {
      throw new Error('invalid cache config: ' + JSON.stringify(cv.errors));
    }
    if (typeof addresses === 'string') {
      addresses = parseAddressText(addresses);
    }
    for (var i = 0; i < addresses.length; i += 1) {
      addresses[i] = numberOrSelf(addresses[i]);
    }
    var av = validateAddresses(addresses);
    if (!av.ok) {
      throw new Error(av.message);
    }

    var main = new Cache(config, seed);
    var faConfig = {
      sets: 1,
      ways: config.sets * config.ways,
      blockSize: config.blockSize,
      policy: config.policy
    };
    var fa = new Cache(faConfig, seed);
    var perAccess = [];
    var totals = {
      hits: 0, misses: 0, compulsory: 0, capacity: 0, conflict: 0, hitRate: 0
    };
    var globalBlocks = {};

    for (var j = 0; j < addresses.length; j += 1) {
      var addr = addresses[j];
      var blockAddr = addr >>> ilog2(config.blockSize);
      var mainRes = main.access(addr);
      var faRes = fa.access(addr);
      var firstEver = !globalBlocks[blockAddr];
      globalBlocks[blockAddr] = true;
      var missClass;
      if (mainRes.hit) {
        missClass = 'hit';
        totals.hits += 1;
      } else {
        totals.misses += 1;
        if (firstEver) {
          missClass = 'compulsory';
          totals.compulsory += 1;
        } else if (!faRes.hit) {
          missClass = 'capacity';
          totals.capacity += 1;
        } else {
          missClass = 'conflict';
          totals.conflict += 1;
        }
      }
      perAccess.push({
        addr: addr,
        hit: mainRes.hit,
        setIndex: mainRes.setIndex,
        way: mainRes.way,
        missClass: missClass
      });
    }
    var totalAccesses = totals.hits + totals.misses;
    totals.hitRate = totalAccesses === 0 ? 0 : totals.hits / totalAccesses;
    return {
      config: config,
      perAccess: perAccess,
      totals: totals,
      occupancy: getOccupancy(main)
    };
  }

  CS.simulate = simulate;
  CS.parseAddressText = parseAddressText;
  CS.generateSequential = generateSequential;
  CS.generateStrided = generateStrided;
  CS.generateRandom = generateRandom;
  CS.validateConfig = validateConfig;
  CS.POLICIES = POLICIES;
})(CACHESIM);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = CACHESIM;
}
