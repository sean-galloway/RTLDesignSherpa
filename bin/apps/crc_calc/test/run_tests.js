#!/usr/bin/env node
// run_tests.js -- zero-dependency node test runner for crc_calc.
//
// require()s the shipped js/model.js (the dual window/globalThis header
// makes the shipped bytes require()-able unchanged), runs the suites
// below, and reports TAP-ish results. Exit code 0 iff every assertion
// passed.
//
// Usage: node bin/apps/crc_calc/test/run_tests.js
'use strict';

var path = require('path');
var CRCX = require(path.join(__dirname, '..', 'js', 'model.js'));

var tests = [];
var n = 0;
var failed = 0;

function test(name, fn) { tests.push({ name: name, fn: fn }); }

function eq(actual, expected, msg) {
  if (actual !== expected) {
    throw new Error((msg || 'mismatch') + ': expected 0x' +
                    expected.toString(16).toUpperCase() + ', got 0x' +
                    actual.toString(16).toUpperCase());
  }
}

function strBytes(s) {
  var b = [];
  var i;
  for (i = 0; i < s.length; i += 1) {
    b.push(s.charCodeAt(i) & 0xFF);
  }
  return b;
}

// Serialize a CRC value into bytes in the order dictated by REFOUT:
// big-endian for REFOUT=0, little-endian for REFOUT=1.
function crcBytes(value, width, refout) {
  var n = width / 8;
  var b = [];
  var i;
  if (refout) {
    for (i = 0; i < n; i += 1) {
      b.push((value >> (i * 8)) & 0xFF);
    }
  } else {
    for (i = n - 1; i >= 0; i -= 1) {
      b.push((value >> (i * 8)) & 0xFF);
    }
  }
  return b;
}

// --- golden check values on the standard string ----------------------------
CRCX.PRESETS.forEach(function (preset) {
  test(preset.name + ' check value on "123456789"', function () {
    var r = CRCX.computeCRC(preset.params, strBytes('123456789'));
    eq(r.result, preset.check, 'result');
  });
});

// --- zero-length message cases ---------------------------------------------
test('CRC-8 empty message', function () {
  var r = CRCX.computeCRC(CRCX.PRESETS[0].params, []);
  eq(r.result, 0x00, 'empty CRC-8');
});

test('CRC-16/CCITT-FALSE empty message', function () {
  var r = CRCX.computeCRC(CRCX.PRESETS[1].params, []);
  eq(r.result, 0xFFFF, 'empty CRC-16/CCITT-FALSE');
});

test('CRC-16/ARC empty message', function () {
  var r = CRCX.computeCRC(CRCX.PRESETS[2].params, []);
  eq(r.result, 0x0000, 'empty CRC-16/ARC');
});

test('CRC-32 empty message', function () {
  var r = CRCX.computeCRC(CRCX.PRESETS[3].params, []);
  eq(r.result, 0x00000000, 'empty CRC-32');
});

// --- reflectBits sanity -----------------------------------------------------
test('reflectBits reverses bits', function () {
  eq(CRCX.reflectBits(0x01, 8), 0x80, 'single bit 8-bit');
  eq(CRCX.reflectBits(0x80, 8), 0x01, 'MSB to LSB 8-bit');
  eq(CRCX.reflectBits(0x12345678, 32), 0x1E6A2C48, '32-bit reversal');
  eq(CRCX.reflectBits(CRCX.reflectBits(0xA5, 8), 8), 0xA5, 'double reflection');
});

// --- custom-polynomial round trip -------------------------------------------
test('custom 16-bit polynomial round trip drives residue to zero', function () {
  // Non-preset polynomial and seed, with XOROUT=0 so the expected residue is 0.
  var params = {
    CRC_POLY: 0x0589,
    CRC_INIT: 0x1234,
    CRC_REFIN: false,
    CRC_REFOUT: false,
    CRC_XOROUT: 0x0000,
    width: 16
  };
  var msg = strBytes('RTL');
  var r = CRCX.computeCRC(params, msg);
  var appended = msg.concat(crcBytes(r.result, params.width, params.CRC_REFOUT));
  var r2 = CRCX.computeCRC(params, appended);
  eq(r2.result, 0x0000, 'round-trip residue');
});

// --- REFIN/REFOUT symmetry --------------------------------------------------
test('toggling REFIN/REFOUT and reflecting data mirrors the checksum', function () {
  var params = CRCX.PRESETS[3].params; // CRC-32
  var bytes = strBytes('abc');
  var reflBytes = bytes.map(function (b) { return CRCX.reflectBits(b, 8); });
  var toggled = {
    CRC_POLY: params.CRC_POLY,
    CRC_INIT: params.CRC_INIT,
    CRC_REFIN: !params.CRC_REFIN,
    CRC_REFOUT: !params.CRC_REFOUT,
    CRC_XOROUT: params.CRC_XOROUT,
    width: params.width
  };
  var expected = CRCX.computeCRC(params, bytes).result;
  var actual = CRCX.reflectBits(CRCX.computeCRC(toggled, reflBytes).result, params.width);
  eq(actual, expected, 'reflected result');
});

// --- per-byte step table for a 1-byte message -------------------------------
test('per-byte step table for one-byte CRC-8 message', function () {
  var params = CRCX.PRESETS[0].params; // CRC-8
  var r = CRCX.computeCRC(params, [0x31]);

  if (!r.perByteSteps || r.perByteSteps.length !== 1) {
    throw new Error('expected one per-byte step');
  }
  var step = r.perByteSteps[0];
  eq(step.byte, 0x31, 'byte stored');
  eq(step.registerAfter, 0x97, 'register after byte 0x31');

  // Hand-verified MSB-first CRC-8 (poly 0x07, init 0x00) bit evolution for
  // byte 0x31. An asterisk marks the cycles where the top bit was 1 and the
  // polynomial was XORed in.
  var expected = [
    {reg: 0x62, xor: false}, // bit 0 (MSB) was 0
    {reg: 0xC4, xor: false}, // bit 1 was 0
    {reg: 0x8F, xor: true},  // bit 2 was 1 -> XOR 0x07
    {reg: 0x19, xor: true},  // bit 3 was 1 -> XOR 0x07
    {reg: 0x32, xor: false}, // bit 4 was 0
    {reg: 0x64, xor: false}, // bit 5 was 0
    {reg: 0xC8, xor: false}, // bit 6 was 0
    {reg: 0x97, xor: true}   // bit 7 (LSB) was 1 -> XOR 0x07
  ];

  var i;
  for (i = 0; i < 8; i += 1) {
    eq(step.bitSteps[i].bit, i, 'bit index ' + i);
    eq(step.bitSteps[i].registerAfter, expected[i].reg, 'bit ' + i + ' register');
    if (step.bitSteps[i].xorApplied !== expected[i].xor) {
      throw new Error('bit ' + i + ' xorApplied mismatch');
    }
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
