#!/usr/bin/env node
// run_tests.js -- zero-dependency node test runner for ddr_drills.
//
// require()s the shipped js files in the SAME order index.html loads them
// (the dual window/globalThis header makes the shipped bytes require()-able
// unchanged), then requires the test files, which register suites on
// globalThis.DDRD_TEST_SUITES, then runs every suite and reports TAP-ish
// results. Exit code 0 iff every assertion passed.
//
// Usage: node bin/apps/ddr_drills/test/run_tests.js
'use strict';

var path = require('path');

var JS_ORDER = [
  'registry.js',
  'rng.js',
  'model.js',
  'engine.js',
  'mutate.js',
  'scenarios.js'
];

var TEST_ORDER = [
  'test_engine.js',
  'test_mutate.js',
  'test_scenarios.js'
];

var root = path.join(__dirname, '..');

JS_ORDER.forEach(function (f) {
  require(path.join(root, 'js', f));
});

globalThis.DDRD_TEST_SUITES = globalThis.DDRD_TEST_SUITES || [];

TEST_ORDER.forEach(function (f) {
  require(path.join(__dirname, f));
});

// -- assertion kit -----------------------------------------------------------

function deepEq(a, b) {
  if (a === b) {
    return true;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    if (a.length !== b.length) {
      return false;
    }
    for (var i = 0; i < a.length; i++) {
      if (!deepEq(a[i], b[i])) {
        return false;
      }
    }
    return true;
  }
  if (a && b && typeof a === 'object' && typeof b === 'object') {
    var ka = Object.keys(a);
    var kb = Object.keys(b);
    if (ka.length !== kb.length) {
      return false;
    }
    for (var j = 0; j < ka.length; j++) {
      if (!deepEq(a[ka[j]], b[ka[j]])) {
        return false;
      }
    }
    return true;
  }
  return false;
}

function makeT(state) {
  return {
    ok: function (cond, msg) {
      state.total++;
      if (cond) {
        state.passed++;
        console.log('ok ' + state.total + ' - ' + msg);
      } else {
        state.failed++;
        console.log('not ok ' + state.total + ' - ' + msg);
      }
    },
    eq: function (actual, expected, msg) {
      var pass = actual === expected;
      if (!pass) {
        msg += ' (expected: ' + JSON.stringify(expected) +
               ', got: ' + JSON.stringify(actual) + ')';
      }
      this.ok(pass, msg);
    },
    deepEq: function (actual, expected, msg) {
      var pass = deepEq(actual, expected);
      if (!pass) {
        msg += ' (expected: ' + JSON.stringify(expected) +
               ', got: ' + JSON.stringify(actual) + ')';
      }
      this.ok(pass, msg);
    },
    throws: function (fn, msg) {
      var threw = false;
      try {
        fn();
      } catch (e) {
        threw = true;
      }
      this.ok(threw, msg);
    }
  };
}

// -- runner ------------------------------------------------------------------

var suites = globalThis.DDRD_TEST_SUITES;
var grand = { total: 0, passed: 0, failed: 0 };
var suiteFailed = 0;

console.log('TAP version 13');

suites.forEach(function (suite) {
  console.log('# suite: ' + suite.name);
  var state = { total: grand.total, passed: 0, failed: 0 };
  var t = makeT(state);
  try {
    suite.run(t);
  } catch (e) {
    state.total++;
    state.failed++;
    console.log('not ok ' + state.total + ' - suite threw: ' +
                (e && e.stack ? e.stack.split('\n')[0] : e));
  }
  grand.total = state.total;
  grand.passed += state.passed;
  grand.failed += state.failed;
  if (state.failed > 0) {
    suiteFailed++;
  }
});

console.log('# ' + suites.length + ' suites, ' + grand.total +
            ' assertions, ' + grand.passed + ' passed, ' + grand.failed +
            ' failed');

if (grand.failed > 0 || suiteFailed > 0) {
  console.log('# FAIL');
  process.exit(1);
}
console.log('# PASS');
process.exit(0);
