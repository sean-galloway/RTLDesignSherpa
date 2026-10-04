// model.js -- fixed-point Q-format math engine for qformat_explorer.
//
// Pure functions, no DOM. Dual-environment header: the same bytes run in
// the browser (window.QFX) and under node (module.exports).
//
// Notation:
//   - Signed Qm.n: 1 sign bit + m integer bits + n fractional bits
//     (total width = m + n + 1), range [-2^m, 2^m - 2^-n].
//   - Unsigned Qm.n: m integer bits + n fractional bits
//     (total width = m + n), range [0, 2^m - 2^-n].
//
// All masking, wrap, and saturation arithmetic is done with Math.pow(2, k)
// instead of JS bitwise shifts so that 32-bit formats (and anything up to
// m + n = 32) work correctly.
var QFX = (typeof window !== 'undefined' ? window : globalThis).QFX ||
          ((typeof window !== 'undefined' ? window : globalThis).QFX = {});

(function (QFX) {
  'use strict';

  var PRESETS = [
    { name: 'Q1.6 / 8-bit signed',  m: 1,  n: 6,  signed: true },
    { name: 'Q7.8 / 16-bit signed', m: 7,  n: 8,  signed: true },
    { name: 'Q15.16 / 32-bit signed', m: 15, n: 16, signed: true }
  ];

  function pow2(k) { return Math.pow(2, k); }

  function totalBits(m, n, signed) {
    return signed ? m + n + 1 : m + n;
  }

  function validate(m, n, signed) {
    signed = signed !== false;
    var errors = [];
    if (typeof m !== 'number' || !isFinite(m) || m !== Math.floor(m) || m < 0) {
      errors.push('m must be a non-negative integer');
    }
    if (typeof n !== 'number' || !isFinite(n) || n !== Math.floor(n) || n < 0) {
      errors.push('n must be a non-negative integer');
    }
    if (errors.length === 0) {
      var maxPayload = signed ? 32 : 32;
      if (m + n > maxPayload) {
        errors.push('m + n must be <= ' + maxPayload);
      }
    }
    return { ok: errors.length === 0, errors: errors };
  }

  function config(m, n, signed) {
    signed = signed !== false;
    var v = validate(m, n, signed);
    if (!v.ok) { return { ok: false, errors: v.errors }; }

    var bits = totalBits(m, n, signed);
    var step = pow2(-n);
    var maxVal = pow2(m) - step;
    var minVal = signed ? -pow2(m) : 0;
    var maxRaw;
    var minRaw;
    if (signed) {
      maxRaw = pow2(bits - 1) - 1;
      minRaw = -pow2(bits - 1);
    } else {
      maxRaw = pow2(bits) - 1;
      minRaw = 0;
    }

    return {
      ok: true,
      m: m,
      n: n,
      signed: signed,
      totalBits: bits,
      step: step,
      maxError: step / 2,
      max: maxVal,
      min: minVal,
      maxRaw: maxRaw,
      minRaw: minRaw,
      mask: pow2(bits) - 1
    };
  }

  // Round a real number to the nearest fixed-point integer (raw units).
  function roundRaw(real, n) {
    return Math.round(real * pow2(n));
  }

  // Arithmetic modulo that never uses bitwise ops.
  function mod(x, mod) {
    var r = x % mod;
    return r < 0 ? r + mod : r;
  }

  // Wrap a raw fixed-point integer into the representable unsigned range.
  function wrapRaw(raw, cfg) {
    return mod(raw, pow2(cfg.totalBits));
  }

  // Convert a raw unsigned value into the signed interpretation.
  function unsignedToSigned(u, cfg) {
    if (!cfg.signed) { return u; }
    var half = pow2(cfg.totalBits - 1);
    if (u >= half) { u -= pow2(cfg.totalBits); }
    return u;
  }

  // Convert a real value to fixed-point.
  // mode: 'wrap' (default) or 'saturate'.
  // signed: true (default) or false.
  function valueToFixed(real, m, n, mode, signed) {
    mode = mode || 'wrap';
    signed = signed !== false;
    var cfg = config(m, n, signed);
    if (!cfg.ok) { return { ok: false, errors: cfg.errors }; }

    var raw = roundRaw(real, n);
    var overflow = raw > cfg.maxRaw || raw < cfg.minRaw;
    var clamped;

    if (mode === 'saturate') {
      if (raw > cfg.maxRaw) {
        clamped = cfg.maxRaw;
      } else if (raw < cfg.minRaw) {
        clamped = cfg.minRaw;
      } else {
        clamped = raw;
      }
    } else {
      clamped = wrapRaw(raw, cfg);
    }

    var interpreted = unsignedToSigned(clamped, cfg);

    return {
      ok: true,
      m: m,
      n: n,
      signed: signed,
      mode: mode,
      input: real,
      raw: interpreted,
      bitsInt: clamped,
      bitsStr: formatBits(clamped, m, n, signed),
      value: interpreted * cfg.step,
      overflow: overflow,
      step: cfg.step,
      maxError: cfg.maxError,
      max: cfg.max,
      min: cfg.min
    };
  }

  // Convert a fixed-point bit pattern (unsigned integer) to its real value.
  function fixedToValue(bitsInt, m, n, signed) {
    signed = signed !== false;
    var cfg = config(m, n, signed);
    if (!cfg.ok) { return { ok: false, errors: cfg.errors }; }

    var u = mod(bitsInt, pow2(cfg.totalBits));
    var raw = unsignedToSigned(u, cfg);

    return {
      ok: true,
      m: m,
      n: n,
      signed: signed,
      bitsInt: u,
      bitsStr: formatBits(u, m, n, signed),
      raw: raw,
      value: raw * cfg.step,
      step: cfg.step,
      maxError: cfg.maxError,
      max: cfg.max,
      min: cfg.min
    };
  }

  // Format an unsigned bit pattern as a binary string with the binary point.
  function formatBits(bitsInt, m, n, signed) {
    signed = signed !== false;
    var cfg = config(m, n, signed);
    if (!cfg.ok) { return ''; }
    var s = padBinary(bitsInt, cfg.totalBits);
    if (cfg.signed) {
      var sign = s.charAt(0);
      var integer = s.substring(1, 1 + m);
      var frac = s.substring(1 + m);
      return sign + ' ' + integer + ' . ' + frac;
    }
    var integer = s.substring(0, m);
    var frac = s.substring(m);
    return integer + ' . ' + frac;
  }

  function padBinary(value, width) {
    var s = '';
    var v = value;
    while (v > 0) {
      s = ((v & 1) ? '1' : '0') + s;
      v = Math.floor(v / 2);
    }
    while (s.length < width) { s = '0' + s; }
    return s;
  }

  // Toggle one bit in the pattern and return the new unsigned pattern plus
  // the decoded value. bitIndex 0 = LSB.
  function toggleBit(bitsInt, bitIndex, m, n, signed) {
    signed = signed !== false;
    var cfg = config(m, n, signed);
    if (!cfg.ok) { return { ok: false, errors: cfg.errors }; }
    if (bitIndex < 0 || bitIndex >= cfg.totalBits) {
      return { ok: false, errors: ['bit index out of range'] };
    }
    var mask = pow2(bitIndex);
    var newBits = ((bitsInt & mask) !== 0) ? bitsInt - mask : bitsInt + mask;
    newBits = mod(newBits, pow2(cfg.totalBits));
    var r = fixedToValue(newBits, m, n, signed);
    return {
      ok: true,
      bitIndex: bitIndex,
      oldBits: bitsInt,
      newBits: newBits,
      value: r.value,
      bitsStr: r.bitsStr
    };
  }

  function add(a, b, m, n, mode, signed) {
    mode = mode || 'wrap';
    signed = signed !== false;
    var cfg = config(m, n, signed);
    if (!cfg.ok) { return { ok: false, errors: cfg.errors }; }

    var fa = valueToFixed(a, m, n, mode, signed);
    var fb = valueToFixed(b, m, n, mode, signed);
    var exact = a + b;
    var quantized = fa.value + fb.value;
    var doubleQuantized = valueToFixed(quantized, m, n, mode, signed);

    return {
      ok: true,
      op: 'add',
      m: m,
      n: n,
      signed: signed,
      mode: mode,
      a: a,
      b: b,
      exact: exact,
      aFixed: fa,
      bFixed: fb,
      quantized: quantized,
      result: doubleQuantized,
      growthRule: 'Qm.n + Qm.n -> Q' + (m + 1) + '.n, then rescale to Qm.n'
    };
  }

  function mul(a, b, m, n, mode, signed) {
    mode = mode || 'wrap';
    signed = signed !== false;
    var cfg = config(m, n, signed);
    if (!cfg.ok) { return { ok: false, errors: cfg.errors }; }

    var fa = valueToFixed(a, m, n, mode, signed);
    var fb = valueToFixed(b, m, n, mode, signed);
    var exact = a * b;

    // Hardware reality: operands are already quantized, multiply in double
    // width, then rescale back to Qm.n.
    var rawProduct = fa.raw * fb.raw;
    var productValue = rawProduct * cfg.step * cfg.step;
    var doubleQuantized = valueToFixed(productValue, m, n, mode, signed);

    return {
      ok: true,
      op: 'mul',
      m: m,
      n: n,
      signed: signed,
      mode: mode,
      a: a,
      b: b,
      exact: exact,
      aFixed: fa,
      bFixed: fb,
      quantized: productValue,
      result: doubleQuantized,
      growthRule: 'Qm.n * Qm.n -> Q' + (2 * m) + '.' + (2 * n) + ', then rescale to Qm.n'
    };
  }

  function overflowRamp(value, m, n, signed) {
    signed = signed !== false;
    var cfg = config(m, n, signed);
    if (!cfg.ok) { return { ok: false, errors: cfg.errors }; }

    var wrap = valueToFixed(value, m, n, 'wrap', signed);
    var sat = valueToFixed(value, m, n, 'saturate', signed);

    return {
      ok: true,
      input: value,
      m: m,
      n: n,
      signed: signed,
      max: cfg.max,
      min: cfg.min,
      wrap: wrap,
      saturate: sat,
      wrapBinary: wrap.bitsStr,
      saturateBinary: sat.bitsStr
    };
  }

  function stepSize(n) { return pow2(-n); }
  function maxError(n) { return stepSize(n) / 2; }

  // Range helpers assume signed by default; pass false for unsigned min/max.
  function minValue(m, signed) {
    signed = signed !== false;
    return signed ? -pow2(m) : 0;
  }
  function maxValue(m, n, signed) {
    signed = signed !== false;
    return pow2(m) - pow2(-n);
  }

  QFX.PRESETS = PRESETS;
  QFX.validate = validate;
  QFX.config = config;
  QFX.valueToFixed = valueToFixed;
  QFX.fixedToValue = fixedToValue;
  QFX.formatBits = formatBits;
  QFX.toggleBit = toggleBit;
  QFX.add = add;
  QFX.mul = mul;
  QFX.overflowRamp = overflowRamp;
  QFX.stepSize = stepSize;
  QFX.maxError = maxError;
  QFX.minValue = minValue;
  QFX.maxValue = maxValue;
})(QFX);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = QFX;
}
