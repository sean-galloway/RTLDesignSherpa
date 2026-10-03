#!/usr/bin/env node
// run_tests.js -- zero-dependency node test runner for fifo_depth.
//
// require()s the shipped js/model.js (the dual window/globalThis header
// makes the shipped bytes require()-able unchanged), runs the suites
// below, and reports TAP-ish results. Exit code 0 iff every assertion
// passed.
//
// Usage: node bin/apps/fifo_depth/test/run_tests.js
'use strict';

var path = require('path');
var FD = require(path.join(__dirname, '..', 'js', 'model.js'));

var tests = [];
var n = 0;
var failed = 0;

function test(name, fn) { tests.push({ name: name, fn: fn }); }

function eq(actual, expected, msg) {
  if (actual !== expected) {
    throw new Error((msg || 'mismatch') + ': expected ' + expected + ', got ' + actual);
  }
}

// --- golden example cases (spec section 4) -------------------------------
var GOLDEN = [
  { c: 1, p: { fA: 80, fB: 50, burst: 120, wIdle: 0, rIdle: 0, nSync: 2 }, exp: [75, 45, 47, 64, 48] },
  { c: 2, p: { fA: 100, fB: 90, burst: 120, wIdle: 0, rIdle: 0, nSync: 2 }, exp: [108, 12, 14, 16, 14] },
  { c: 3, p: { fA: 50, fB: 50, burst: 120, wIdle: 1, rIdle: 3, nSync: 2 }, exp: [60, 60, 62, 64, 62] },
  { c: 4, p: { fA: 30, fB: 50, burst: 120, wIdle: 1, rIdle: 3, nSync: 2 }, exp: [100, 20, 22, 32, 22] },
  { c: 5, p: { fA: 200, fB: 100, burst: 256, wIdle: 0, rIdle: 0, nSync: 3 }, exp: [128, 128, 131, 256, 132] },
  { c: 6, p: { fA: 80, fB: 50, burst: 120, wIdle: 0, rIdle: 0, nSync: 3 }, exp: [75, 45, 48, 64, 48] }
];

GOLDEN.forEach(function (g) {
  test('golden case ' + g.c, function () {
    var r = FD.compute(g.p);
    eq(r.itemsRead, g.exp[0], 'itemsRead');
    eq(r.rawDepth, g.exp[1], 'rawDepth');
    eq(r.totalDepth, g.exp[2], 'totalDepth');
    eq(r.grayDepth, g.exp[3], 'grayDepth');
    eq(r.johnsonDepth, g.exp[4], 'johnsonDepth');
    eq(r.steady.drainable, false, 'drainable');
  });
});

// --- review focus / edge cases -------------------------------------------
test('equal frequencies zero idles clamp raw depth to 1', function () {
  var r = FD.compute({ fA: 50, fB: 50, burst: 100, wIdle: 0, rIdle: 0, nSync: 2 });
  eq(r.itemsRead, 100, 'itemsRead');
  eq(r.rawDepth, 1, 'rawDepth');
});

test('burst one gives gray minimum 2', function () {
  var r = FD.compute({ fA: 80, fB: 50, burst: 1, wIdle: 0, rIdle: 0, nSync: 0 });
  eq(r.rawDepth, 1, 'rawDepth');
  eq(r.grayDepth, 2, 'grayDepth');
});

test('steady state yes when reader is faster', function () {
  var r = FD.compute({ fA: 50, fB: 80, burst: 120, wIdle: 0, rIdle: 0, nSync: 2 });
  eq(r.steady.drainable, true, 'drainable');
});

test('fractional mhz accepted without rounding', function () {
  var p = { fA: 66.667, fB: 50, burst: 120, wIdle: 0, rIdle: 0, nSync: 2 };
  var r = FD.compute(p);
  var tW = (1 + 0) * 1000 / 66.667;
  var expected = Math.floor(120 * tW / ((1 + 0) * 1000 / 50));
  eq(r.itemsRead, expected, 'itemsRead');
});

test('savings pct zero when gray equals johnson', function () {
  var r = FD.compute({ fA: 50, fB: 80, burst: 8, wIdle: 0, rIdle: 0, nSync: 0 });
  eq(r.grayDepth === r.johnsonDepth, true, 'depths equal premise');
  eq(r.savingsPct, 0, 'savingsPct');
});

test('validation flags each bad field and accepts numeric strings', function () {
  var v = FD.validate({ fA: 0, fB: -1, burst: 0, wIdle: -1, rIdle: 1.5, nSync: 2 });
  eq(v.ok, false, 'ok');
  eq(typeof v.errors.fA, 'string', 'fA error');
  eq(typeof v.errors.fB, 'string', 'fB error');
  eq(typeof v.errors.burst, 'string', 'burst error');
  eq(typeof v.errors.wIdle, 'string', 'wIdle error');
  eq(typeof v.errors.rIdle, 'string', 'rIdle error');
  eq(v.errors.nSync, undefined, 'nSync clean');
  var v2 = FD.validate({ fA: '80', fB: '50', burst: '120', wIdle: '0', rIdle: '0', nSync: '2' });
  eq(v2.ok, true, 'numeric strings ok');
});

// --- runner ----------------------------------------------------------------
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
