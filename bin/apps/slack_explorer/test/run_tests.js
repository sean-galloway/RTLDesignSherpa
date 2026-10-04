#!/usr/bin/env node
// run_tests.js -- zero-dependency node test runner for slack_explorer.
//
// require()s the shipped js/model.js (the dual window/globalThis header
// makes the shipped bytes require()-able unchanged), runs the suites
// below, and reports TAP-ish results. Exit code 0 iff every assertion
// passed.
//
// Usage: node bin/apps/slack_explorer/test/run_tests.js
'use strict';

var path = require('path');
var SLACK = require(path.join(__dirname, '..', 'js', 'model.js'));

var tests = [];
var n = 0;
var failed = 0;

function test(name, fn) { tests.push({ name: name, fn: fn }); }

function eq(actual, expected, msg) {
  if (actual !== expected) {
    throw new Error((msg || 'mismatch') + ': expected ' + expected + ', got ' + actual);
  }
}

function near(actual, expected, tol, msg) {
  if (Math.abs(actual - expected) > tol) {
    throw new Error((msg || 'near mismatch') + ': expected ' + expected +
                    ' +/- ' + tol + ', got ' + actual);
  }
}

// --- textbook setup slack numbers ------------------------------------------
// Hand math: T=10, tCO=1, tLOGIC=5, tROUTE=1, skew=0, tSU=1
// setup slack = 10 - 1 - 5 - 1 + 0 - 1 = 2 ns.
test('textbook setup slack is 2 ns', function () {
  var p = { T: 10, tCO: 1, tLOGIC: 5, tROUTE: 1, skew: 0, tSU: 1, tHD: 0.5, K: 1 };
  var s = SLACK.computeSlack(p);
  eq(s.setupSlack, 2, 'setupSlack');
  eq(s.setupPass, true, 'setupPass');
  eq(s.holdSlack, 6.5, 'holdSlack');
  eq(s.holdPass, true, 'holdPass');
  eq(s.pass, true, 'overall pass');
});

// Negative skew helps setup, hurts hold. With skew=-3:
// setup = 10 - 1 - 5 - 1 - 3 - 1 = -1 ns (FAIL).
// hold  = 1 + 5 + 1 + 3 - 0.5 = 8.5 ns (PASS).
test('negative skew flips setup slack to fail', function () {
  var p = { T: 10, tCO: 1, tLOGIC: 5, tROUTE: 1, skew: -3, tSU: 1, tHD: 0.5, K: 1 };
  var s = SLACK.computeSlack(p);
  eq(s.setupSlack, -1, 'setupSlack');
  eq(s.setupPass, false, 'setupPass');
  eq(s.holdPass, true, 'holdPass');
  eq(s.pass, false, 'overall pass');
});

// Positive skew hurts setup, helps hold. With skew=+3:
// setup = 10 - 1 - 5 - 1 + 3 - 1 = 5 ns (PASS).
// hold  = 1 + 5 + 1 - 3 - 0.5 = 3.5 ns (PASS).
test('positive skew improves hold slack', function () {
  var p = { T: 10, tCO: 1, tLOGIC: 5, tROUTE: 1, skew: 3, tSU: 1, tHD: 0.5, K: 1 };
  var s = SLACK.computeSlack(p);
  eq(s.setupSlack, 5, 'setupSlack');
  eq(s.holdSlack, 3.5, 'holdSlack');
  eq(s.holdPass, true, 'holdPass');
});

// --- hold slack sign --------------------------------------------------------
// hold slack = tCO + tLOGIC + tROUTE - skew - tHD.
// Make tHD large enough to force a hold violation when skew is positive.
test('hold slack becomes negative when skew is large positive', function () {
  var p = { T: 10, tCO: 0.5, tLOGIC: 1, tROUTE: 0.5, skew: 2, tSU: 1, tHD: 2, K: 1 };
  var s = SLACK.computeSlack(p);
  // hold = 0.5 + 1 + 0.5 - 2 - 2 = -2 ns
  eq(s.holdSlack, -2, 'holdSlack');
  eq(s.holdPass, false, 'holdPass');
  eq(s.setupPass, true, 'setupPass');
  eq(s.hint.indexOf('MORE delay') !== -1, true, 'hint mentions adding delay');
});

// --- pipelined frequency scaling -------------------------------------------
// tLOGIC=8, tROUTE=0, tCO=1, tSU=1, T large enough not to matter.
// K=1: stageLogic=8, minPeriod=10, freq=100 MHz.
// K=2: stageLogic=4, minPeriod=6, freq=166.67 MHz.
// K=4: stageLogic=2, minPeriod=4, freq=250 MHz.
// Frequency scales ~K, bounded below by the tCO+tSU floor of 2 ns.
test('pipeline frequency scales with K and respects tCO+tSU floor', function () {
  var p = { T: 20, tCO: 1, tLOGIC: 8, tROUTE: 0, skew: 0, tSU: 1, tHD: 0.5, K: 1 };
  var r1 = SLACK.computePipeline(p, 1);
  var r2 = SLACK.computePipeline(p, 2);
  var r4 = SLACK.computePipeline(p, 4);
  eq(r1.minPeriod, 10, 'K=1 minPeriod');
  near(r1.maxFreq, 100, 0.01, 'K=1 freq');
  eq(r2.minPeriod, 6, 'K=2 minPeriod');
  near(r2.maxFreq, 1000 / 6, 0.01, 'K=2 freq');
  eq(r4.minPeriod, 4, 'K=4 minPeriod');
  near(r4.maxFreq, 250, 0.01, 'K=4 freq');
  // With tCO+tSU=2, even K->inf cannot beat 2 ns -> 500 MHz.
  var rHuge = SLACK.computePipeline(p, 1000);
  near(rHuge.minPeriod, 2, 0.01, 'asymptotic minPeriod floor');
});

// --- edge case: K that cannot close at any listed T ------------------------
// Make the period so small that even the fastest pipeline (K=4) cannot close.
test('edge case period too small for any K in 1..4', function () {
  var p = { T: 1.5, tCO: 1, tLOGIC: 8, tROUTE: 0, skew: 0, tSU: 1, tHD: 0.5, K: 4 };
  var table = SLACK.computePipelineTable(p);
  table.forEach(function (r) {
    eq(r.closesWithT, false, 'K=' + r.K + ' does not close');
  });
});

// --- validation ------------------------------------------------------------
test('validation flags bad fields and accepts numeric strings', function () {
  var v = SLACK.validate({ T: 0, tCO: -1, tLOGIC: 'x', tROUTE: 1, skew: 0, tSU: 1, tHD: 1, K: 5 });
  eq(v.ok, false, 'ok');
  eq(typeof v.errors.T, 'string', 'T error');
  eq(typeof v.errors.tCO, 'string', 'tCO error');
  eq(typeof v.errors.tLOGIC, 'string', 'tLOGIC error');
  eq(typeof v.errors.K, 'string', 'K error');

  var v2 = SLACK.validate({ T: '10', tCO: '1', tLOGIC: '5', tROUTE: '1', skew: '0', tSU: '1', tHD: '0.5', K: '1' });
  eq(v2.ok, true, 'numeric strings ok');
});

// --- unified compute -------------------------------------------------------
test('unified compute returns slack and pipeline results', function () {
  var p = { T: 10, tCO: 1, tLOGIC: 5, tROUTE: 1, skew: 0, tSU: 1, tHD: 0.5, K: 2 };
  var r = SLACK.compute(p);
  eq(r.slack.setupSlack, 2, 'slack result');
  eq(r.pipeline.selected.K, 2, 'selected K');
  eq(r.pipeline.table.length, 4, 'table length');
});

// --- app-level behavior (minimal DOM stub; no browser needed) ---------------
function makeDomStub(values) {
  var els = {};
  var IDS = ['T', 'tCO', 'tLOGIC', 'tROUTE', 'skew', 'tSU', 'tHD', 'K'];
  IDS.forEach(function (id) {
    var val = values[id] !== undefined ? values[id] : '0';
    els['in-' + id] = { value: val };
    els['in-' + id + '-range'] = { value: val };
    els['err-' + id] = { textContent: '' };
  });
  ['slack-banner', 'slack-results', 'slack-hint',
   'pipeline-takeaway', 'pipeline-table'].forEach(function (id) {
    els[id] = { innerHTML: '', textContent: '', className: '' };
  });
  globalThis.document = {
    getElementById: function (id) { return els[id]; },
    addEventListener: function () {}
  };
  return els;
}

test('app renders slack and pipeline panels with valid input', function () {
  var els = makeDomStub({ T: '10', tCO: '1', tLOGIC: '5', tROUTE: '1', skew: '0', tSU: '1', tHD: '0.5', K: '1' });
  require(path.join(__dirname, '..', 'js', 'app.js'));
  SLACK.app.update();
  eq(els['slack-results'].innerHTML.indexOf('Setup Slack') !== -1, true, 'slack results rendered');
  eq(els['pipeline-table'].innerHTML.indexOf('Max Freq') !== -1, true, 'pipeline table rendered');
  eq(els['slack-banner'].className, 'banner good', 'slack banner shows pass');
});

test('app clears results on invalid input', function () {
  var els = makeDomStub({ T: '10', tCO: '1', tLOGIC: '5', tROUTE: '1', skew: '0', tSU: '1', tHD: '0.5', K: '1' });
  require(path.join(__dirname, '..', 'js', 'app.js'));
  SLACK.app.update();
  if (els['slack-results'].innerHTML === '') {
    throw new Error('premise: valid input should render results');
  }
  els['in-T'].value = 'abc';
  SLACK.app.update();
  eq(els['err-T'].textContent, 'must be > 0', 'T error shown');
  eq(els['slack-results'].innerHTML, '', 'slack results cleared');
  eq(els['pipeline-table'].innerHTML, '', 'pipeline table cleared');
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
