#!/usr/bin/env node
// run_tests.js -- zero-dependency node test runner for mtbf_calc.
//
// require()s the shipped js/model.js (the dual window/globalThis header
// makes the shipped bytes require()-able unchanged), runs the suites
// below, and reports TAP-ish results. Exit code 0 iff every assertion
// passed.
//
// Usage: node bin/apps/mtbf_calc/test/run_tests.js
'use strict';

var path = require('path');
var MTBF = require(path.join(__dirname, '..', 'js', 'model.js'));

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
  tol = tol === undefined ? 1e-9 : tol;
  if (Math.abs(actual - expected) > tol) {
    throw new Error((msg || 'near mismatch') + ': expected ' + expected + ', got ' + actual);
  }
}

// --- known-answer case (hand computed) -------------------------------------
//
// Pick simple numbers so the exponential term is exactly 1:
//   c2 = 0, c1 = 9e-16, f_clk = 1e9, f_data = 1e6, t0 = 100 ps, N = 1.
// Then tMET_total = t0 = 1e-10 s, exp(0 * tMET) = 1, and
//   MTBF = 1 / (9e-16 * 1e9 * 1e6) = 1 / 0.9 = 1.111... s.
test('known-answer hand-computed case', function () {
  var p = {
    c1: 9e-16, c2: 0, fData: 1e6, fClk: 1e9,
    tCO: 0, tSU: 0, t0: 1e-10, n: 1, missionYears: 1
  };
  var r = MTBF.compute(p);
  near(r.mtbf, 10 / 9, 1e-12, 'mtbf seconds');
  near(r.scaled.value, 10 / 9, 1e-9, 'scaled value');
  eq(r.scaled.unit, 's', 'scaled unit');
});

// --- formula inversion sanity ----------------------------------------------
test('formula inversion sanity', function () {
  var c1 = 1e-11;
  var c2 = 1.7e10;
  var fClk = 1e9;
  var fData = 1e6;
  var tMET = 9.1e-10;  // roughly N=2 with r=900 ps and t0=10 ps
  var mtbf = MTBF.mtbfSeconds(c1, c2, tMET, fClk, fData);
  var back = MTBF.tMETFromMTBF(c1, c2, fClk, fData, mtbf);
  near(back, tMET, 1e-18, 'inverted tMET');
});

// --- monotonic increase in N and r -----------------------------------------
test('MTBF increases monotonically with N', function () {
  var p = {
    c1: 1e-11, c2: 1.7e10, fData: 1e6, fClk: 1e9,
    tCO: 50e-12, tSU: 50e-12, t0: 10e-12, n: 1, missionYears: 1
  };
  var prev = 0;
  for (var nStage = 1; nStage <= 4; nStage += 1) {
    p.n = nStage;
    var r = MTBF.compute(p);
    if (r.mtbf <= prev) {
      throw new Error('MTBF did not increase at N=' + nStage);
    }
    prev = r.mtbf;
  }
});

test('MTBF decreases monotonically as resolution time r shrinks', function () {
  var base = {
    c1: 1e-11, c2: 1.7e10, fData: 1e6, fClk: 1e9,
    tCO: 50e-12, tSU: 50e-12, t0: 10e-12, n: 2, missionYears: 1
  };
  var prev = Infinity;
  [50e-12, 100e-12, 200e-12, 400e-12].forEach(function (tCO) {
    var p = {
      c1: base.c1, c2: base.c2, fData: base.fData, fClk: base.fClk,
      tCO: tCO, tSU: base.tSU, t0: base.t0, n: base.n, missionYears: base.missionYears
    };
    var r = MTBF.compute(p);
    if (r.mtbf >= prev) {
      throw new Error('MTBF did not decrease with smaller r (tCO=' + tCO + ')');
    }
    prev = r.mtbf;
  });
});

// --- input validation ------------------------------------------------------
test('validation rejects non-positive rates and out-of-range N', function () {
  var v = MTBF.validate({
    c1: 0, c2: -1, fData: 0, fClk: -1e9,
    tCO: -1, tSU: -1, t0: 0, n: 5, missionYears: 0
  });
  eq(v.ok, false, 'ok');
  eq(typeof v.errors.c1, 'string', 'c1 error');
  eq(typeof v.errors.c2, 'string', 'c2 error');
  eq(typeof v.errors.fData, 'string', 'fData error');
  eq(typeof v.errors.fClk, 'string', 'fClk error');
  eq(typeof v.errors.tCO, 'string', 'tCO error');
  eq(typeof v.errors.tSU, 'string', 'tSU error');
  eq(typeof v.errors.t0, 'string', 't0 error');
  eq(typeof v.errors.n, 'string', 'n error');
  eq(typeof v.errors.missionYears, 'string', 'missionYears error');
});

test('validation accepts numeric strings', function () {
  var v = MTBF.validate({
    c1: '1e-11', c2: '1.7e10', fData: '1e6', fClk: '1e9',
    tCO: '50e-12', tSU: '50e-12', t0: '10e-12', n: '2', missionYears: '1'
  });
  eq(v.ok, true, 'numeric strings ok');
});

test('validation rejects tCO + tSU >= clock period', function () {
  var v = MTBF.validate({
    c1: 1e-11, c2: 1.7e10, fData: 1e6, fClk: 1e9,
    tCO: 600e-12, tSU: 600e-12, t0: 10e-12, n: 2, missionYears: 1
  });
  eq(v.ok, false, 'ok');
  eq(typeof v.errors.fClk, 'string', 'fClk error');
});

// --- headline lesson sanity ------------------------------------------------
test('1 GHz 28 nm N=2 fails one-year mission, N=3 passes', function () {
  var base = {
    c1: MTBF.DEFAULTS.c1, c2: MTBF.DEFAULTS.c2,
    fData: MTBF.DEFAULTS.fData, fClk: MTBF.DEFAULTS.fClk,
    tCO: MTBF.DEFAULTS.tCO, tSU: MTBF.DEFAULTS.tSU,
    t0: MTBF.DEFAULTS.t0, missionYears: MTBF.DEFAULTS.missionYears
  };
  var r2 = MTBF.compute({ c1: base.c1, c2: base.c2, fData: base.fData, fClk: base.fClk,
                          tCO: base.tCO, tSU: base.tSU, t0: base.t0, n: 2, missionYears: base.missionYears });
  var r3 = MTBF.compute({ c1: base.c1, c2: base.c2, fData: base.fData, fClk: base.fClk,
                          tCO: base.tCO, tSU: base.tSU, t0: base.t0, n: 3, missionYears: base.missionYears });
  eq(r2.pass, false, 'N=2 fails');
  eq(r3.pass, true, 'N=3 passes');
  eq(MTBF.minPassingN({ c1: base.c1, c2: base.c2, fData: base.fData, fClk: base.fClk,
                        tCO: base.tCO, tSU: base.tSU, t0: base.t0, n: 2, missionYears: base.missionYears }), 3, 'min passing N');
});

// --- scaleSeconds sanity ---------------------------------------------------
test('scaleSeconds picks sensible units', function () {
  var s = MTBF.scaleSeconds(1.5e-6);
  eq(s.value, 1.5, 'us value');
  eq(s.unit, 'us', 'us unit');

  s = MTBF.scaleSeconds(MTBF.SECONDS_PER_YEAR * 100);
  eq(s.unit, 'years', 'years unit');
});

// --- app-level behavior (minimal DOM stub) ---------------------------------
function makeDomStub(values) {
  var els = {};
  ['preset', 'c1', 'c2', 'fdata', 'fclk', 'tco', 'tsu', 't0', 'n', 'mission'].forEach(function (id) {
    els['in-' + id] = { value: values[id] };
    els['err-' + id] = { textContent: '' };
  });
  ['main-result', 'verdict', 'mtbf-table', 'banner'].forEach(function (id) {
    els[id] = { innerHTML: '', textContent: '', className: '' };
  });
  globalThis.document = {
    getElementById: function (id) { return els[id]; },
    addEventListener: function () {}
  };
  return els;
}

test('invalid input clears results and keeps field errors', function () {
  var els = makeDomStub({
    preset: '28 nm (illustrative)',
    c1: '1e-11', c2: '1.7e10', fdata: '1e6', fclk: '1e9',
    tco: '50e-12', tsu: '50e-12', t0: '10e-12', n: '2', mission: '1'
  });
  require(path.join(__dirname, '..', 'js', 'app.js'));
  MTBF.app.update();
  if (els.banner.className === 'hidden') {
    throw new Error('premise: valid input should render banner');
  }
  els['in-fclk'].value = 'abc';
  MTBF.app.update();
  eq(els['err-fclk'].textContent, 'must be > 0', 'fclk error shown');
  eq(els.banner.className, 'banner hidden', 'banner hidden');
  eq(els['main-result'].innerHTML, '', 'main result cleared');
});

// --- boot smoke test (minimal DOM stub) --------------------------------------
// Guards the class of bug that shipped broken on 2026-10-04: the
// DOMContentLoaded boot threw in the browser (renderErrors touched a null
// err-preset span) while every node test stayed green, because nothing
// exercised the boot path.
test('app boot: DOMContentLoaded handler runs and renders results', function () {
  var els = {};
  function mk(id, value) {
    els[id] = {
      value: value, textContent: '', innerHTML: '', className: '',
      addEventListener: function () {},
      querySelectorAll: function () { return []; }
    };
  }
  var D = MTBF.DEFAULTS;
  mk('in-preset', D.preset);
  mk('in-c1', String(D.c1));
  mk('in-c2', String(D.c2));
  mk('in-fdata', String(D.fData));
  mk('in-fclk', String(D.fClk));
  mk('in-tco', String(D.tCO));
  mk('in-tsu', String(D.tSU));
  mk('in-t0', String(D.t0));
  mk('in-n', String(D.n));
  mk('in-mission', String(D.missionYears));
  ['c1', 'c2', 'fdata', 'fclk', 'tco', 'tsu', 't0', 'n', 'mission']
    .forEach(function (id) { mk('err-' + id); });
  mk('main-result'); mk('mtbf-table'); mk('verdict'); mk('banner');
  mk('btn-1ghz');
  var domReady = null;
  globalThis.document = {
    getElementById: function (id) {
      // Browser-faithful: unknown ids return null (the app guards the
      // preset field, which has no error span).
      return els[id] || null;
    },
    addEventListener: function (ev, fn) {
      if (ev === 'DOMContentLoaded') { domReady = fn; }
    }
  };
  try {
    // Earlier tests in this file already required app.js with no document
    // defined (boot block skipped, module cached) — re-require fresh.
    delete require.cache[
      require.resolve(path.join(__dirname, '..', 'js', 'app.js'))
    ];
    require(path.join(__dirname, '..', 'js', 'app.js'));
    if (!domReady) { throw new Error('boot never registered DOMContentLoaded'); }
    domReady();
    if (els['main-result'].innerHTML.indexOf('MTBF') === -1) {
      throw new Error('main-result not rendered after boot');
    }
    if (els['mtbf-table'].innerHTML.indexOf('<tr') === -1) {
      throw new Error('N-table not rendered after boot');
    }
  } finally {
    delete globalThis.document;
  }
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
