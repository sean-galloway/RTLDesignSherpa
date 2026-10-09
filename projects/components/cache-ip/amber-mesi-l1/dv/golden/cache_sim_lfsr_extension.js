// cache_sim_lfsr_extension.js -- recorded cache_sim extension for amber
// parity (DECISION D-9, Task 10).
//
// cache_sim's native RANDOM policy draws mulberry32 values, and only when a
// set is full.  The amber RTL (amber_repl REPL_POLICY=random) instead keeps
// one 32-bit Fibonacci LFSR per set (taps 32,22,2,1 -- zero-indexed bits
// 31,21,1,0 -- feedback shifted into the LSB), every set seeded with
// REPL_SEED (amber_repl default 32'h0000_ACE1), and samples+advances it on
// EVERY miss (repl_req on the first MISS_VICTIM cycle) with no empty-way
// preference.  Bit-identical native parity is impossible (D-9), so the RANDOM
// grid cells run this RECORDED EXTENSION: the exact model.js source with the
// anchored replacements below applied to a COMPILED COPY -- the app under
// bin/apps/cache_sim/ is never edited.
//
// The harness (cache_sim_harness.py) applies each patch with a strict
// single-occurrence anchor check, so any drift in the shipped model.js fails
// loudly instead of silently mis-patching.
//
// Run under node >= 18 (also browser-requireable, but the harness is the
// only consumer).
'use strict';

module.exports = {
  id: 'amber-rtl-lfsr-v1',
  // The LFSR seed must stay in lockstep with the amber_repl REPL_SEED
  // parameter default (rtl/fub/amber_repl.sv).
  repl_seed: 0x0000ACE1,
  patches: [
    {
      label: 'inject makeLfsrRng factory before the Cache constructor',
      anchor:
        '  function Cache(config, seed) {',
      replacement:
        '  // --- recorded amber RTL extension (D-9): per-set Fibonacci LFSR --\n' +
        '  // amber_repl RANDOM: victim = state[WAY-1:0] sampled on every miss,\n' +
        '  // then state <<= 1 with fb = ^{31,21,1,0} into the LSB.\n' +
        '  var LFSR_SEED = 0x0000ACE1;\n' +
        '  function makeLfsrRng() {\n' +
        '    var state = LFSR_SEED >>> 0;\n' +
        '    return {\n' +
        '      nextInt: function (max) {\n' +
        '        var way = state & ((max >>> 0) - 1);\n' +
        '        var fb = ((state >>> 31) ^ (state >>> 21) ^\n' +
        '                  (state >>> 1) ^ state) & 1;\n' +
        '        state = ((state << 1) | fb) >>> 0;\n' +
        '        return way;\n' +
        '      }\n' +
        '    };\n' +
        '  }\n' +
        '\n' +
        '  function Cache(config, seed) {'
    },
    {
      label: 'RANDOM sets use the LFSR factory instead of mulberry32',
      anchor:
        '        rng: config.policy === \'RANDOM\' ? makeRng(seed) : null',
      replacement:
        '        rng: config.policy === \'RANDOM\' ? makeLfsrRng() : null'
    },
    {
      label: 'RANDOM draws on every miss, no empty-way preference',
      anchor:
        '    for (w = 0; w < cfg.ways; w += 1) {\n' +
        '      if (set.tags[w] === null) {\n' +
        '        way = w;\n' +
        '        break;\n' +
        '      }\n' +
        '    }\n' +
        '    if (way === -1) {\n' +
        '      if (cfg.policy === \'LRU\') {\n' +
        '        way = set.lru.shift();\n' +
        '      } else if (cfg.policy === \'FIFO\') {\n' +
        '        way = set.fifo.shift();\n' +
        '      } else if (cfg.policy === \'RANDOM\') {\n' +
        '        way = set.rng.nextInt(cfg.ways);\n' +
        '      } else {\n' +
        '        way = 0;\n' +
        '      }\n' +
        '    }',
      replacement:
        '    if (cfg.policy === \'RANDOM\') {\n' +
        '      // recorded extension: amber_repl RANDOM has no empty-way\n' +
        '      // preference -- every miss installs into the LFSR victim way.\n' +
        '      way = set.rng.nextInt(cfg.ways);\n' +
        '    } else {\n' +
        '      for (w = 0; w < cfg.ways; w += 1) {\n' +
        '        if (set.tags[w] === null) {\n' +
        '          way = w;\n' +
        '          break;\n' +
        '        }\n' +
        '      }\n' +
        '      if (way === -1) {\n' +
        '        if (cfg.policy === \'LRU\') {\n' +
        '          way = set.lru.shift();\n' +
        '        } else if (cfg.policy === \'FIFO\') {\n' +
        '          way = set.fifo.shift();\n' +
        '        } else {\n' +
        '          way = 0;\n' +
        '        }\n' +
        '      }\n' +
        '    }'
    }
  ]
};
