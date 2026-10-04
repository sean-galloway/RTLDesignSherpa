#!/usr/bin/env node
// run_tests.js -- zero-dependency node test runner for cdc_drill.
//
// require()s the shipped js/rng.js, js/content.js, and js/model.js (the
// dual window/globalThis header makes the shipped bytes require()-able
// unchanged), runs the suites below, and reports TAP-ish results. Exit code 0
// iff every assertion passed.
//
// Usage: node bin/apps/cdc_drill/test/run_tests.js
'use strict';

var path = require('path');

var CDCD = require(path.join(__dirname, '..', 'js', 'rng.js'));
require(path.join(__dirname, '..', 'js', 'content.js'));
require(path.join(__dirname, '..', 'js', 'model.js'));

var tests = [];
var n = 0;
var failed = 0;

function test(name, fn) { tests.push({ name: name, fn: fn }); }

function eq(actual, expected, msg) {
  if (actual !== expected) {
    throw new Error((msg || 'mismatch') + ': expected ' + expected + ', got ' + actual);
  }
}

function assert(cond, msg) {
  if (!cond) {
    throw new Error(msg || 'assertion failed');
  }
}

// --- content floor ---------------------------------------------------------
test('spot generator count >= 16', function () {
  assert(CDCD.spotGenerators.length >= 16,
    'expected >= 16, got ' + CDCD.spotGenerators.length);
});

test('picker generator count >= 12', function () {
  assert(CDCD.pickerGenerators.length >= 12,
    'expected >= 12, got ' + CDCD.pickerGenerators.length);
});

// --- validation: every generator at pinned seed ----------------------------
test('every spot generator produces a valid question', function () {
  var rng = CDCD.mulberry32(0x12345678);
  for (var i = 0; i < CDCD.spotGenerators.length; i++) {
    var q = CDCD.generateSpot(CDCD.spotGenerators[i].id, rng);
    var v = CDCD.validateQuestion(q);
    if (!v.ok) {
      throw new Error(CDCD.spotGenerators[i].id + ': ' + v.errors.join('; '));
    }
  }
});

test('every picker generator produces a valid question', function () {
  var rng = CDCD.mulberry32(0x9ABCDEF0);
  for (var i = 0; i < CDCD.pickerGenerators.length; i++) {
    var q = CDCD.generatePicker(CDCD.pickerGenerators[i].id, rng);
    var v = CDCD.validateQuestion(q);
    if (!v.ok) {
      throw new Error(CDCD.pickerGenerators[i].id + ': ' + v.errors.join('; '));
    }
  }
});

// --- determinism at pinned seeds across two runs ----------------------------
test('spot generation is deterministic at pinned seed', function () {
  var seed = 0xDEADBEEF;
  var rng1 = CDCD.mulberry32(seed);
  var rng2 = CDCD.mulberry32(seed);
  for (var i = 0; i < CDCD.spotGenerators.length; i++) {
    var id = CDCD.spotGenerators[i].id;
    var a = CDCD.generateSpot(id, rng1);
    var b = CDCD.generateSpot(id, rng2);
    eq(a.stem, b.stem, id + ' stem');
    eq(a.options.length, b.options.length, id + ' option count');
    for (var j = 0; j < a.options.length; j++) {
      eq(a.options[j].text, b.options[j].text, id + ' option[' + j + '] text');
      eq(a.options[j].correct, b.options[j].correct, id + ' option[' + j + '] correct');
    }
  }
});

test('picker generation is deterministic at pinned seed', function () {
  var seed = 0xCAFEBABE;
  var rng1 = CDCD.mulberry32(seed);
  var rng2 = CDCD.mulberry32(seed);
  for (var i = 0; i < CDCD.pickerGenerators.length; i++) {
    var id = CDCD.pickerGenerators[i].id;
    var a = CDCD.generatePicker(id, rng1);
    var b = CDCD.generatePicker(id, rng2);
    eq(a.stem, b.stem, id + ' stem');
    eq(a.options.length, b.options.length, id + ' option count');
    for (var j = 0; j < a.options.length; j++) {
      eq(a.options[j].text, b.options[j].text, id + ' option[' + j + '] text');
      eq(a.options[j].correct, b.options[j].correct, id + ' option[' + j + '] correct');
    }
  }
});

// --- shuffle-safe distinct answers -----------------------------------------
test('all generated answer sets are shuffle-safe (distinct texts)', function () {
  var rng = CDCD.mulberry32(0xBADC0FFEE);
  var all = CDCD.generateAllQuestions(rng);
  for (var i = 0; i < all.length; i++) {
    var q = all[i];
    var seen = {};
    for (var j = 0; j < q.options.length; j++) {
      var t = q.options[j].text;
      if (seen[t]) {
        throw new Error(q.id + ' duplicate option text: ' + t);
      }
      seen[t] = true;
    }
  }
});

// --- tier filters ----------------------------------------------------------
test('tier filters include only selected tiers', function () {
  var rng = CDCD.mulberry32(0xFEEDFACE);
  var onlyBasic = CDCD.generateAllQuestions(rng, { 1: true, 2: false, 3: false });
  for (var i = 0; i < onlyBasic.length; i++) {
    if (onlyBasic[i].tier !== 1) {
      throw new Error('tier ' + onlyBasic[i].tier + ' leaked into basic-only');
    }
  }
  var onlyFull = CDCD.generateAllQuestions(rng, { 1: false, 2: false, 3: true });
  for (var j = 0; j < onlyFull.length; j++) {
    if (onlyFull[j].tier !== 3) {
      throw new Error('tier ' + onlyFull[j].tier + ' leaked into full-only');
    }
  }
  var all = CDCD.generateAllQuestions(rng);
  eq(all.length, CDCD.spotGenerators.length + CDCD.pickerGenerators.length,
    'all tiers length');
});

// --- model: session scoring ------------------------------------------------
test('model scores a spot question correctly', function () {
  var rng = CDCD.mulberry32(0x11111111);
  var session = CDCD.createSession(rng, { modes: { spot: true, picker: false } });
  CDCD.nextQuestion(session);
  var cur = CDCD.getCurrent(session);
  assert(cur.q.mode === 'spot', 'expected spot');
  var correctSet = [];
  for (var i = 0; i < cur.options.length; i++) {
    if (cur.options[i].correct) {
      correctSet.push(i);
    }
  }
  for (var j = 0; j < correctSet.length; j++) {
    CDCD.toggleSelection(session, correctSet[j]);
  }
  var result = CDCD.submitAnswer(session);
  assert(result.right, 'exact set should score right');
  eq(CDCD.getScore(session).right, 1, 'score right');
  eq(CDCD.getScore(session).total, 1, 'score total');
});

test('model scores a picker question correctly', function () {
  var rng = CDCD.mulberry32(0x22222222);
  var session = CDCD.createSession(rng, { modes: { spot: false, picker: true } });
  CDCD.nextQuestion(session);
  var cur = CDCD.getCurrent(session);
  assert(cur.q.mode === 'picker', 'expected picker');
  var correctIdx = -1;
  for (var i = 0; i < cur.options.length; i++) {
    if (cur.options[i].correct) {
      correctIdx = i;
      break;
    }
  }
  assert(correctIdx !== -1, 'picker has a correct option');
  CDCD.setSingleSelection(session, correctIdx);
  var result = CDCD.submitAnswer(session);
  assert(result.right, 'correct picker choice should score right');
  eq(CDCD.getScore(session).right, 1, 'score right');
});

test('model marks a wrong spot selection incorrect', function () {
  var rng = CDCD.mulberry32(0x33333333);
  var session = CDCD.createSession(rng, { modes: { spot: true, picker: false } });
  CDCD.nextQuestion(session);
  var cur = CDCD.getCurrent(session);
  var wrongIdx = -1;
  for (var i = 0; i < cur.options.length; i++) {
    if (!cur.options[i].correct) {
      wrongIdx = i;
      break;
    }
  }
  assert(wrongIdx !== -1, 'spot question has a wrong option');
  CDCD.toggleSelection(session, wrongIdx);
  var result = CDCD.submitAnswer(session);
  assert(!result.right, 'wrong selection should score wrong');
  eq(CDCD.getScore(session).right, 0, 'score right');
  eq(CDCD.getScore(session).total, 1, 'score total');
});

test('model marks a wrong picker choice incorrect', function () {
  var rng = CDCD.mulberry32(0x44444444);
  var session = CDCD.createSession(rng, { modes: { spot: false, picker: true } });
  CDCD.nextQuestion(session);
  var cur = CDCD.getCurrent(session);
  var wrongIdx = -1;
  for (var i = 0; i < cur.options.length; i++) {
    if (!cur.options[i].correct) {
      wrongIdx = i;
      break;
    }
  }
  assert(wrongIdx !== -1, 'picker has a wrong option');
  CDCD.setSingleSelection(session, wrongIdx);
  var result = CDCD.submitAnswer(session);
  assert(!result.right, 'wrong picker choice should score wrong');
});

// --- ASCII only ------------------------------------------------------------
test('all generated content is ASCII-only', function () {
  var rng = CDCD.mulberry32(0x55555555);
  var all = CDCD.generateAllQuestions(rng);
  for (var i = 0; i < all.length; i++) {
    var v = CDCD.validateQuestion(all[i]);
    if (!v.ok) {
      throw new Error(all[i].id + ': ' + v.errors.join('; '));
    }
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
