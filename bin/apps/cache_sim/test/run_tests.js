#!/usr/bin/env node
// run_tests.js -- zero-dependency node test runner for cache_sim.
//
// require()s ../js/model.js (the dual window/globalThis header makes the
// shipped bytes require()-able unchanged), runs the suites below, and reports
// TAP-ish results. Exit code 0 iff every assertion passed.
//
// Usage: node bin/apps/cache_sim/test/run_tests.js
'use strict';

var path = require('path');
var CS = require(path.join(__dirname, '..', 'js', 'model.js'));

var tests = [];
var n = 0;
var failed = 0;

function test(name, fn) { tests.push({ name: name, fn: fn }); }

function eq(actual, expected, msg) {
  if (actual !== expected) {
    throw new Error((msg || 'mismatch') + ': expected ' + expected + ', got ' + actual);
  }
}

function arrayEq(actual, expected, msg) {
  if (actual.length !== expected.length) {
    throw new Error((msg || 'length mismatch') + ': expected ' + expected.length + ', got ' + actual.length);
  }
  for (var i = 0; i < actual.length; i += 1) {
    if (actual[i] !== expected[i]) {
      throw new Error((msg || 'array mismatch') + ' at index ' + i + ': expected ' + expected[i] + ', got ' + actual[i]);
    }
  }
}

// --- hand-computed direct-mapped vs 2-way on a short crafted trace ---------
//
// Trace word addresses: [0, 2, 0, 2, 0]
// Block size 1 -> block address == word address.
// With S=2, set index = blockAddr % 2, tag = floor(blockAddr / 2).
//   0 -> set 0, tag 0
//   2 -> set 0, tag 1
//
// W=1 (direct mapped): set 0 holds one line.
//   0: miss (compulsory) -> tag 0
//   2: miss (compulsory) -> evict tag 0, tag 1
//   0: miss (not first; FA would hit because total capacity is 2 lines)
//   2: miss (not first; FA would hit)
//   0: miss (not first; FA would hit)
//   -> hits 0, comp 2, conflict 3, capacity 0
//
// W=2 (2-way FA for S=1, or 2-way per set for S=2): set 0 can hold both
// tag 0 and tag 1.
//   0: miss (compulsory)
//   2: miss (compulsory) -> second way
//   0: hit
//   2: hit
//   0: hit
//   -> hits 3, comp 2, conflict 0, capacity 0
//
test('hand-computed direct-mapped S=2 W=1 B=1', function () {
  var r = CS.simulate({ sets: 2, ways: 1, blockSize: 1, policy: 'LRU' }, [0, 2, 0, 2, 0], 1);
  eq(r.totals.hits, 0, 'hits');
  eq(r.totals.misses, 5, 'misses');
  eq(r.totals.compulsory, 2, 'compulsory');
  eq(r.totals.conflict, 3, 'conflict');
  eq(r.totals.capacity, 0, 'capacity');
});

test('hand-computed 2-way S=2 W=2 B=1', function () {
  var r = CS.simulate({ sets: 2, ways: 2, blockSize: 1, policy: 'LRU' }, [0, 2, 0, 2, 0], 1);
  eq(r.totals.hits, 3, 'hits');
  eq(r.totals.misses, 2, 'misses');
  eq(r.totals.compulsory, 2, 'compulsory');
  eq(r.totals.conflict, 0, 'conflict');
  eq(r.totals.capacity, 0, 'capacity');
});

// --- compulsory counting ---------------------------------------------------
test('compulsory misses equal unique block count', function () {
  // Blocks 0, 1, 0, 2, 1: first touches are 0, 1, 2 -> 3 compulsory.
  var r = CS.simulate({ sets: 4, ways: 1, blockSize: 1, policy: 'LRU' }, [0, 1, 0, 2, 1], 1);
  eq(r.totals.compulsory, 3, 'compulsory');
  eq(r.totals.hits, 2, 'hits');
});

// --- capacity-vs-conflict split on cyclic traces ---------------------------
test('cyclic trace within total capacity produces conflict misses only', function () {
  // S=2, W=1, B=1 -> 2 lines total. Working set {0,2} also size 2 and both
  // map to set 0, so the repeats are conflict misses.
  var r = CS.simulate({ sets: 2, ways: 1, blockSize: 1, policy: 'LRU' }, [0, 2, 0, 2], 1);
  eq(r.totals.compulsory, 2, 'compulsory');
  eq(r.totals.conflict, 2, 'conflict');
  eq(r.totals.capacity, 0, 'capacity');
});

test('cyclic trace exceeding total capacity produces capacity misses', function () {
  // S=2, W=1, B=1 -> 2 lines total. Working set {0,2,4} size 3 exceeds it,
  // so the repeat of 0 is a capacity miss.
  var r = CS.simulate({ sets: 2, ways: 1, blockSize: 1, policy: 'LRU' }, [0, 2, 4, 0], 1);
  eq(r.totals.compulsory, 3, 'compulsory');
  eq(r.totals.capacity, 1, 'capacity');
  eq(r.totals.conflict, 0, 'conflict');
});

// --- LRU vs FIFO divergence ------------------------------------------------
test('LRU and FIFO can diverge on the same trace', function () {
  // S=1, W=2, B=1. Trace [0,1,2,1,0,2].
  // LRU: 0,1,2 are compulsory; 1 hits; 0 evicts 2 (capacity); 2 evicts 0.
  // FIFO: 0,1,2 are compulsory; 1 hits; 0 misses (queue did not refresh);
  //      2 hits because it was loaded after the eviction of 1.
  var lru = CS.simulate({ sets: 1, ways: 2, blockSize: 1, policy: 'LRU' }, [0, 1, 2, 1, 0, 2], 1);
  var fifo = CS.simulate({ sets: 1, ways: 2, blockSize: 1, policy: 'FIFO' }, [0, 1, 2, 1, 0, 2], 1);
  eq(lru.totals.hits, 1, 'LRU hits');
  eq(fifo.totals.hits, 2, 'FIFO hits');
  eq(lru.totals.capacity, 2, 'LRU capacity');
  eq(fifo.totals.capacity, 1, 'FIFO capacity');
});

// --- seeded random generator -----------------------------------------------
test('random generator is reproducible with the same seed', function () {
  var a = CS.generateRandom(10, 7, 100);
  var b = CS.generateRandom(10, 7, 100);
  arrayEq(a, b, 'same seed sequence');
});

test('random generator differs with different seeds', function () {
  var a = CS.generateRandom(20, 7, 100);
  var b = CS.generateRandom(20, 8, 100);
  var same = 0;
  for (var i = 0; i < a.length; i += 1) {
    if (a[i] === b[i]) { same += 1; }
  }
  if (same === a.length) {
    throw new Error('different seeds produced identical sequences');
  }
});

// --- RANDOM policy reproducibility -----------------------------------------
test('RANDOM policy is reproducible with the same seed', function () {
  var cfg = { sets: 4, ways: 2, blockSize: 1, policy: 'RANDOM' };
  var trace = CS.generateRandom(32, 5, 64);
  var a = CS.simulate(cfg, trace.slice(), 5);
  var b = CS.simulate(cfg, trace.slice(), 5);
  eq(a.totals.hits, b.totals.hits, 'same hit count');
  eq(a.totals.conflict, b.totals.conflict, 'same conflict count');
});

// --- block size grouping ---------------------------------------------------
test('block size groups consecutive word addresses', function () {
  // S=1, W=1, B=2. 0 and 1 share block 0; 4 and 5 share block 2.
  var r = CS.simulate({ sets: 1, ways: 1, blockSize: 2, policy: 'LRU' }, [0, 1, 4, 5], 1);
  eq(r.totals.hits, 2, 'hits');
  eq(r.totals.misses, 2, 'misses');
});

// --- fully associative has no conflict misses ------------------------------
test('fully associative cache reports zero conflict misses', function () {
  var r = CS.simulate({ sets: 1, ways: 2, blockSize: 1, policy: 'LRU' }, [0, 1, 2, 0, 1, 2], 1);
  eq(r.totals.conflict, 0, 'conflict');
  eq(r.totals.compulsory, 3, 'compulsory');
  eq(r.totals.capacity, 3, 'capacity');
});

// --- config validation ------------------------------------------------------
test('validateConfig flags bad fields and accepts numeric strings', function () {
  var v = CS.validateConfig({ sets: 3, ways: 0, blockSize: 'abc', policy: 'MAGIC' });
  eq(v.ok, false, 'ok');
  eq(typeof v.errors.sets, 'string', 'sets error');
  eq(typeof v.errors.ways, 'string', 'ways error');
  eq(typeof v.errors.blockSize, 'string', 'blockSize error');
  eq(typeof v.errors.policy, 'string', 'policy error');

  var v2 = CS.validateConfig({ sets: '4', ways: '2', blockSize: '1', policy: 'LRU' });
  eq(v2.ok, true, 'numeric strings ok');
});

// --- address parsing --------------------------------------------------------
test('parseAddressText handles hex, decimal, and blank lines', function () {
  var text = '0x10\n32\n\n0xFF\n// comment-like is stripped\n256\n';
  var arr = CS.parseAddressText(text);
  arrayEq(arr, [0x10, 32, 0xFF, 256], 'parsed addresses');
});

// --- runner -----------------------------------------------------------------
tests.forEach(function (t) {
  n += 1;
  try {
    t.fn();
    console.log('ok ' + n + ' - ' + t.name);
  } catch (e) {
    failed += 1;
    console.log('not ok ' + n + ' - ' + t.name + ' :: ' + e.message);
  }
});

console.log('# ' + (n - failed) + '/' + n + ' passed, ' + failed + ' failed');
process.exit(failed === 0 ? 0 : 1);
