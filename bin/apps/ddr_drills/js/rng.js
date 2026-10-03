// rng.js -- seeded PRNG (mulberry32) plus threaded-randomness helpers.
// ALL randomness in scenario generation and mutation takes an rng parameter
// so tests are fully deterministic with fixed seeds. Nothing here may call
// Math.random().
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  // mulberry32(seed) -> function returning floats in [0, 1).
  // Tiny, fast, good-enough statistical quality for drill generation.
  function mulberry32(seed) {
    var a = seed >>> 0;
    return function () {
      a |= 0;
      a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // Inclusive integer in [lo, hi].
  function rint(rng, lo, hi) {
    return lo + Math.floor(rng() * (hi - lo + 1));
  }

  function rpick(rng, arr) {
    return arr[Math.floor(rng() * arr.length)];
  }

  // Fisher-Yates; returns a NEW array (input never mutated).
  function rshuffle(rng, arr) {
    var out = arr.slice();
    for (var i = out.length - 1; i > 0; i--) {
      var j = Math.floor(rng() * (i + 1));
      var tmp = out[i];
      out[i] = out[j];
      out[j] = tmp;
    }
    return out;
  }

  function rchance(rng, p) {
    return rng() < p;
  }

  DDRD.mulberry32 = mulberry32;
  DDRD.rint = rint;
  DDRD.rpick = rpick;
  DDRD.rshuffle = rshuffle;
  DDRD.rchance = rchance;
})(DDRD);
