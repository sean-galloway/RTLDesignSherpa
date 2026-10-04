#!/usr/bin/env node
// run_tests.js -- zero-dependency node test runner for qformat_explorer.
//
// require()s the shipped js/model.js (the dual window/globalThis header
// makes the shipped bytes require()-able unchanged), runs the suites
// below, and reports TAP-ish results. Exit code 0 iff every assertion
// passed.
//
// Usage: node bin/apps/qformat_explorer/test/run_tests.js
'use strict';

var path = require('path');
var QFX = require(path.join(__dirname, '..', 'js', 'model.js'));

var tests = [];
var n = 0;
var failed = 0;

function test(name, fn) { tests.push({ name: name, fn: fn }); }

function eq(actual, expected, msg) {
  if (actual !== expected) {
    throw new Error((msg || 'mismatch') + ': expected ' + expected + ', got ' + actual);
  }
}

function near(actual, expected, msg) {
  if (Math.abs(actual - expected) > 1e-12) {
    throw new Error((msg || 'near mismatch') + ': expected ' + expected + ', got ' + actual);
  }
}

// --- Q7.8 encode/decode round-trips -----------------------------------------
test('Q7.8 encode 1.5', function () {
  var r = QFX.valueToFixed(1.5, 7, 8, 'wrap');
  eq(r.ok, true, 'ok');
  eq(r.bitsInt, 0x0180, 'bitsInt');
  eq(r.bitsStr, '0 0000001 . 10000000', 'bitsStr');
  near(r.value, 1.5, 'value');
});

test('Q7.8 encode -1.5', function () {
  var r = QFX.valueToFixed(-1.5, 7, 8, 'wrap');
  eq(r.ok, true, 'ok');
  eq(r.bitsInt, 0xFE80, 'bitsInt');
  eq(r.bitsStr, '1 1111110 . 10000000', 'bitsStr');
  near(r.value, -1.5, 'value');
});

test('Q7.8 encode 0.0078125 (2 LSBs)', function () {
  // 0.0078125 = 1/128 = 2/256, so the raw fixed value is 2.
  var r = QFX.valueToFixed(0.0078125, 7, 8, 'wrap');
  eq(r.ok, true, 'ok');
  eq(r.raw, 2, 'raw');
  eq(r.bitsInt, 0x0002, 'bitsInt');
  eq(r.bitsStr, '0 0000000 . 00000010', 'bitsStr');
  near(r.value, 0.0078125, 'value');
});

test('Q7.8 decode 0x0180', function () {
  var r = QFX.fixedToValue(0x0180, 7, 8);
  eq(r.ok, true, 'ok');
  near(r.value, 1.5, 'value');
  eq(r.bitsStr, '0 0000001 . 10000000', 'bitsStr');
});

test('Q7.8 decode 0xFE80', function () {
  var r = QFX.fixedToValue(0xFE80, 7, 8);
  eq(r.ok, true, 'ok');
  near(r.value, -1.5, 'value');
  eq(r.bitsStr, '1 1111110 . 10000000', 'bitsStr');
});

// --- step sizes and representable range --------------------------------------
test('Q7.8 step size and max error', function () {
  near(QFX.stepSize(8), 1 / 256, 'stepSize');
  near(QFX.maxError(8), 1 / 512, 'maxError');
});

test('Q15.16 step size and max error', function () {
  near(QFX.stepSize(16), 1 / 65536, 'stepSize');
  near(QFX.maxError(16), 1 / 131072, 'maxError');
});

test('Q7.8 min/max representable', function () {
  near(QFX.minValue(7), -128, 'minValue');
  near(QFX.maxValue(7, 8), 127 + 255 / 256, 'maxValue');
  var cfg = QFX.config(7, 8);
  near(cfg.min, -128, 'cfg.min');
  near(cfg.max, 127 + 255 / 256, 'cfg.max');
});

// --- wrap vs saturate at the boundary ----------------------------------------
test('Q7.8 wrap at positive boundary', function () {
  // One step past max wraps to most negative value.
  var maxVal = QFX.maxValue(7, 8);
  var r = QFX.valueToFixed(maxVal + QFX.stepSize(8), 7, 8, 'wrap');
  eq(r.overflow, true, 'overflow flag');
  near(r.value, QFX.minValue(7), 'wrapped value');
});

test('Q7.8 saturate at positive boundary', function () {
  var maxVal = QFX.maxValue(7, 8);
  var r = QFX.valueToFixed(maxVal + QFX.stepSize(8), 7, 8, 'saturate');
  eq(r.overflow, true, 'overflow flag');
  near(r.value, maxVal, 'saturated value');
});

test('Q7.8 saturate at negative boundary', function () {
  var minVal = QFX.minValue(7);
  var r = QFX.valueToFixed(minVal - QFX.stepSize(8), 7, 8, 'saturate');
  eq(r.overflow, true, 'overflow flag');
  near(r.value, minVal, 'saturated value');
});

// --- multiplication rescale math ---------------------------------------------
// Hand-checked example in Q7.8:
//   a = 1.5  -> raw 384  (0x0180)
//   b = 2.0  -> raw 512  (0x0200)
// Exact product = 3.0.
// Hardware path: multiply raw values -> 384 * 512 = 196608.
// Q7.8 * Q7.8 -> Q14.16 (1 sign + 14 integer + 16 fractional bits).
// The product raw 196608 in Q14.16 equals 196608 / 65536 = 3.0 exactly.
// Rescaling back to Q7.8 gives raw 768 = 0x0300, value 3.0.
test('Q7.8 multiplication rescale hand check', function () {
  var r = QFX.mul(1.5, 2.0, 7, 8, 'wrap');
  eq(r.ok, true, 'ok');
  near(r.exact, 3.0, 'exact product');
  near(r.quantized, 3.0, 'quantized product');
  near(r.result.value, 3.0, 'result value');
  eq(r.result.bitsInt, 0x0300, 'result bitsInt');
  eq(r.result.bitsStr, '0 0000011 . 00000000', 'result bitsStr');
  eq(r.growthRule, 'Qm.n * Qm.n -> Q14.16, then rescale to Qm.n', 'growthRule');
});

// --- addition overflow --------------------------------------------------------
test('Q7.8 addition overflow wraps by default', function () {
  var maxVal = QFX.maxValue(7, 8);
  var r = QFX.add(maxVal, 1.0, 7, 8, 'wrap');
  eq(r.result.overflow, true, 'overflow flag');
  // maxVal raw = 32767; +1.0 raw = 256; sum raw = 33023.
  // 33023 signed in 16 bits = -32513; /256 = -127.00390625.
  near(r.result.value, -127.00390625, 'wrapped result');
});

test('Q7.8 addition overflow saturates', function () {
  var maxVal = QFX.maxValue(7, 8);
  var r = QFX.add(maxVal, 1.0, 7, 8, 'saturate');
  eq(r.result.overflow, true, 'overflow flag');
  near(r.result.value, maxVal, 'saturated result');
});

// --- overflow ramp -----------------------------------------------------------
test('overflow ramp shows wrap vs saturate', function () {
  var ramp = QFX.overflowRamp(200, 7, 8);
  eq(ramp.ok, true, 'ok');
  eq(ramp.wrap.overflow, true, 'wrap overflow');
  eq(ramp.saturate.overflow, true, 'saturate overflow');
  near(ramp.saturate.value, ramp.max, 'saturate clamped to max');
});

// --- validation --------------------------------------------------------------
test('validate rejects negative m', function () {
  var v = QFX.validate(-1, 8);
  eq(v.ok, false, 'ok');
});

test('validate rejects m + n > 32', function () {
  var v = QFX.validate(20, 20);
  eq(v.ok, false, 'ok');
});

test('validate accepts m + n = 32', function () {
  var v = QFX.validate(16, 16);
  eq(v.ok, true, 'ok');
});

// --- 32-bit signed (Q15.16) golden tests -------------------------------------
test('Q15.16 encode 1.5', function () {
  var r = QFX.valueToFixed(1.5, 15, 16, 'wrap', true);
  eq(r.ok, true, 'ok');
  eq(r.bitsInt, 0x18000, 'bitsInt');
  near(r.value, 1.5, 'value');
});

test('Q15.16 decode 0x18000', function () {
  var r = QFX.fixedToValue(0x18000, 15, 16, true);
  eq(r.ok, true, 'ok');
  near(r.value, 1.5, 'value');
});

test('Q15.16 wrap at positive boundary', function () {
  var maxVal = QFX.maxValue(15, 16, true);
  var r = QFX.valueToFixed(maxVal + QFX.stepSize(16), 15, 16, 'wrap', true);
  eq(r.overflow, true, 'overflow flag');
  near(r.value, QFX.minValue(15, true), 'wrapped value');
});

test('Q15.16 saturate at positive boundary', function () {
  var maxVal = QFX.maxValue(15, 16, true);
  var r = QFX.valueToFixed(maxVal + QFX.stepSize(16), 15, 16, 'saturate', true);
  eq(r.overflow, true, 'overflow flag');
  near(r.value, maxVal, 'saturated value');
});

// --- unsigned Qm.n tests ------------------------------------------------------
test('unsigned Q4.4 encode 5.5', function () {
  var r = QFX.valueToFixed(5.5, 4, 4, 'wrap', false);
  eq(r.ok, true, 'ok');
  eq(r.bitsInt, 0x58, 'bitsInt');
  eq(r.bitsStr, '0101 . 1000', 'bitsStr');
  near(r.value, 5.5, 'value');
});

test('unsigned Q4.4 max value', function () {
  var maxVal = QFX.maxValue(4, 4, false);
  near(maxVal, 15 + 15 / 16, 'maxValue');
  var cfg = QFX.config(4, 4, false);
  near(cfg.max, maxVal, 'cfg.max');
  eq(cfg.min, 0, 'cfg.min');
});

test('unsigned Q4.4 wrap above max', function () {
  var maxVal = QFX.maxValue(4, 4, false);
  var r = QFX.valueToFixed(maxVal + QFX.stepSize(4), 4, 4, 'wrap', false);
  eq(r.overflow, true, 'overflow flag');
  near(r.value, 0, 'wrapped to zero');
});

test('unsigned Q4.4 saturates at zero and max', function () {
  var maxVal = QFX.maxValue(4, 4, false);
  var lo = QFX.valueToFixed(-1, 4, 4, 'saturate', false);
  var hi = QFX.valueToFixed(maxVal + 1, 4, 4, 'saturate', false);
  eq(lo.overflow, true, 'negative overflow flag');
  near(lo.value, 0, 'saturate low');
  eq(hi.overflow, true, 'positive overflow flag');
  near(hi.value, maxVal, 'saturate high');
});

test('unsigned Q4.4 addition', function () {
  var r = QFX.add(5.5, 2.25, 4, 4, 'wrap', false);
  near(r.exact, 7.75, 'exact');
  near(r.result.value, 7.75, 'result');
});

test('unsigned Q4.4 multiplication', function () {
  var r = QFX.mul(2.5, 3.0, 4, 4, 'wrap', false);
  near(r.exact, 7.5, 'exact');
  near(r.result.value, 7.5, 'result');
});

// --- toggleBit tests ----------------------------------------------------------
// 1.5 in Q7.8 is raw 384 = 0x0180. LSB (bit 0) is 0, so flipping it adds
// one LSB.
test('toggleBit flips LSB in signed Q7.8', function () {
  var r = QFX.valueToFixed(1.5, 7, 8, 'wrap', true);
  var t = QFX.toggleBit(r.bitsInt, 0, 7, 8, true);
  eq(t.ok, true, 'ok');
  near(t.value, 1.5 + QFX.stepSize(8), 'value incremented by one LSB');
});

// Flipping the sign bit of 0x0180 yields 0x8180, which is -126.5 in Q7.8.
test('toggleBit flips sign bit in signed Q7.8', function () {
  var r = QFX.valueToFixed(1.5, 7, 8, 'wrap', true);
  var t = QFX.toggleBit(r.bitsInt, 15, 7, 8, true);
  eq(t.ok, true, 'ok');
  near(t.value, -126.5, 'value after sign-bit toggle');
});

// 5.5 in unsigned Q4.4 is raw 88 = 0x58. MSB (bit 7) is 0, so flipping it
// adds 128 raw units = 8.0.
test('toggleBit flips MSB in unsigned Q4.4', function () {
  var r = QFX.valueToFixed(5.5, 4, 4, 'wrap', false);
  var t = QFX.toggleBit(r.bitsInt, 7, 4, 4, false);
  eq(t.ok, true, 'ok');
  near(t.value, 5.5 + 8, 'value incremented by 8');
});

// --- app-level bit-toggle test (minimal DOM stub) ----------------------------
function makeDomStub(values) {
  var els = {};
  ['m', 'n'].forEach(function (id) {
    els['in-' + id] = { value: String(values[id]), addEventListener: function () {} };
    els['err-' + id] = { textContent: '' };
  });
  ['preset', 'mode', 'signed', 'real', 'bits', 'a', 'b', 'op', 'ramp'].forEach(function (id) {
    els['in-' + id] = { value: values[id] || '', addEventListener: function () {} };
  });
  ['range', 'labels', 'represented', 'error', 'max-error', 'step',
   'arith-rule', 'a-value', 'a-bits', 'b-value', 'b-bits', 'exact',
   'quantized', 'result-value', 'result-bits',
   'wrap-binary', 'wrap-value', 'sat-binary', 'sat-value'].forEach(function (id) {
    els['out-' + id] = { textContent: '', innerHTML: '' };
  });
  els['out-binary'] = {
    textContent: '',
    innerHTML: '',
    querySelectorAll: function () { return []; }
  };
  globalThis.document = {
    getElementById: function (id) { return els[id]; },
    addEventListener: function () {}
  };
  return els;
}

test('app toggleBit updates inputs and binary display', function () {
  var els = makeDomStub({ m: 7, n: 8, signed: 'signed', bits: '0x180' });
  require(path.join(__dirname, '..', 'js', 'app.js'));
  QFX.app.toggleBit(0);
  eq(els['in-bits'].value, '0x181', 'bits input updated');
  eq(els['in-real'].value, '1.50390625', 'real input updated');
  if (els['out-binary'].innerHTML.indexOf('data-idx="0"') === -1) {
    throw new Error('binary display should contain clickable LSB span');
  }
});

// --- runner ------------------------------------------------------------------
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
