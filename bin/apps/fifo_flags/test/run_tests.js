#!/usr/bin/env node
// run_tests.js -- zero-dependency node test runner for fifo_flags.
//
// require()s the shipped js/model.js (the dual window/globalThis header
// makes the shipped bytes require()-able unchanged), runs the suites
// below, and reports TAP-ish results. Exit code 0 iff every assertion
// passed.
//
// Usage: node bin/apps/fifo_flags/test/run_tests.js
'use strict';

var path = require('path');
var FF = require(path.join(__dirname, '..', 'js', 'model.js'));

var tests = [];
var n = 0;
var failed = 0;

function test(name, fn) { tests.push({ name: name, fn: fn }); }

function eq(actual, expected, msg) {
  if (actual !== expected) {
    throw new Error((msg || 'mismatch') + ': expected ' + expected + ', got ' + actual);
  }
}

// --- golden example cases --------------------------------------------------
var GOLDEN = [
  { c: 1, p: { depth: 32, fWr: 100, fRd: 100, nSync: 2, bubblePct: 10 },
    exp: { marginAF: 3, marginAE: 3, bubbleItems: 3, afThreshold: 26, aeThreshold: 6, pass: true } },
  { c: 2, p: { depth: 64, fWr: 200, fRd: 100, nSync: 2, bubblePct: 10 },
    exp: { marginAF: 6, marginAE: 3, bubbleItems: 6, afThreshold: 52, aeThreshold: 9, pass: true } },
  { c: 3, p: { depth: 64, fWr: 100, fRd: 200, nSync: 2, bubblePct: 10 },
    exp: { marginAF: 3, marginAE: 6, bubbleItems: 6, afThreshold: 55, aeThreshold: 12, pass: true } }
];

GOLDEN.forEach(function (g) {
  test('golden case ' + g.c, function () {
    var r = FF.compute(g.p);
    eq(r.marginAF, g.exp.marginAF, 'marginAF');
    eq(r.marginAE, g.exp.marginAE, 'marginAE');
    eq(r.bubbleItems, g.exp.bubbleItems, 'bubbleItems');
    eq(r.afThreshold, g.exp.afThreshold, 'afThreshold');
    eq(r.aeThreshold, g.exp.aeThreshold, 'aeThreshold');
    eq(r.pass, g.exp.pass, 'pass');
  });
});

// --- review focus / edge cases ---------------------------------------------
test('symmetric clocks hand-computed', function () {
  var r = FF.compute({ depth: 32, fWr: 100, fRd: 100, nSync: 2, bubblePct: 10 });
  eq(r.marginAF, 3, 'marginAF');
  eq(r.marginAE, 3, 'marginAE');
  eq(r.bubbleItems, 3, 'bubbleItems');
  eq(r.afThreshold, 26, 'afThreshold');
  eq(r.aeThreshold, 6, 'aeThreshold');
  eq(r.pass, true, 'pass');
});

test('worst-case ratio case', function () {
  var r = FF.compute({ depth: 64, fWr: 300, fRd: 100, nSync: 2, bubblePct: 10 });
  eq(r.marginAF, 9, 'marginAF');
  eq(r.marginAE, 3, 'marginAE');
  eq(r.bubbleItems, 6, 'bubbleItems');
  eq(r.afThreshold, 49, 'afThreshold');
  eq(r.aeThreshold, 9, 'aeThreshold');
  eq(r.pass, true, 'pass');
});

test('threshold-collision rejected for tiny depths', function () {
  var r = FF.compute({ depth: 8, fWr: 200, fRd: 100, nSync: 2, bubblePct: 10 });
  eq(r.afThreshold, 1, 'afThreshold');
  eq(r.aeThreshold, 4, 'aeThreshold');
  eq(r.pass, false, 'pass');
});

test('monotonicity: more stages deepens margin', function () {
  var r2 = FF.compute({ depth: 64, fWr: 200, fRd: 100, nSync: 2, bubblePct: 10 });
  var r3 = FF.compute({ depth: 64, fWr: 200, fRd: 100, nSync: 3, bubblePct: 10 });
  if (r3.marginAF <= r2.marginAF) {
    throw new Error('marginAF should grow with nSync: ' + r2.marginAF + ' -> ' + r3.marginAF);
  }
  if (r3.marginAE <= r2.marginAE) {
    throw new Error('marginAE should grow with nSync: ' + r2.marginAE + ' -> ' + r3.marginAE);
  }
});

test('validation flags each bad field and accepts numeric strings', function () {
  var v = FF.validate({ depth: 0, fWr: 0, fRd: -1, nSync: -1, bubblePct: 101 });
  eq(v.ok, false, 'ok');
  eq(typeof v.errors.depth, 'string', 'depth error');
  eq(typeof v.errors.fWr, 'string', 'fWr error');
  eq(typeof v.errors.fRd, 'string', 'fRd error');
  eq(typeof v.errors.nSync, 'string', 'nSync error');
  eq(typeof v.errors.bubblePct, 'string', 'bubblePct error');
  var v2 = FF.validate({ depth: '32', fWr: '100', fRd: '100', nSync: '2', bubblePct: '10' });
  eq(v2.ok, true, 'numeric strings ok');
});

// --- app-level behaviors (minimal DOM stub; no browser needed) --------------
function makeDomStub(values) {
  var els = {};
  ['depth', 'fwr', 'frd', 'nsync', 'bubble'].forEach(function (id) {
    els['in-' + id] = { value: values[id] };
    els['err-' + id] = { textContent: '' };
  });
  ['flags', 'verdict', 'banner', 'examples'].forEach(function (id) {
    els[id] = { innerHTML: '', textContent: '', className: '' };
  });
  globalThis.document = {
    getElementById: function (id) { return els[id]; },
    addEventListener: function () {}
  };
  return els;
}

test('invalid input clears results and keeps field errors', function () {
  var els = makeDomStub({ depth: '32', fwr: '100', frd: '100', nsync: '2', bubble: '10' });
  require(path.join(__dirname, '..', 'js', 'app.js'));
  FF.app.update();
  if (els.flags.innerHTML === '') {
    throw new Error('premise: valid input should render results');
  }
  els['in-depth'].value = 'abc';
  FF.app.update();
  eq(els['err-depth'].textContent, 'must be an integer >= 1', 'depth error shown');
  eq(els.flags.innerHTML, '', 'flags cleared');
  eq(els.verdict.innerHTML, '', 'verdict cleared');
  eq(els.banner.className, 'banner hidden', 'banner hidden');
});

test('example-note escaping covers & < > and quotes', function () {
  require(path.join(__dirname, '..', 'js', 'app.js'));
  eq(FF.app.esc('fWr < fRd & "q"'), 'fWr &lt; fRd &amp; &quot;q&quot;', 'esc helper');
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
