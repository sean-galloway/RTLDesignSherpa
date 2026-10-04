# Q-Format Explorer

A standalone, file://-friendly drill app for exploring signed fixed-point
Qm.n representation.

## Files

- `index.html` -- UI
- `style.css` -- mobile-first styles
- `js/model.js` -- pure Q-format math (no DOM)
- `js/app.js` -- DOM glue
- `test/run_tests.js` -- zero-dependency TAP-ish node runner

## Run

Open `index.html` in a browser, or serve it statically. No build step, no
CDN, no npm.

## Test

```bash
node bin/apps/qformat_explorer/test/run_tests.js
```

Exit code 0 when all assertions pass.

## Model API

- `QFX.config(m, n, signed)` -- validate and return step, range, masks, etc.
  `signed` defaults to `true`.
- `QFX.valueToFixed(real, m, n, mode, signed)` -- encode a real to
  fixed-point. `mode` is `'wrap'` (default) or `'saturate'`. Returns the
  unsigned bit pattern, represented value, overflow flag, etc.
- `QFX.fixedToValue(bitsInt, m, n, signed)` -- decode an unsigned bit pattern.
- `QFX.formatBits(bitsInt, m, n, signed)` -- pretty binary string with binary
  point.
- `QFX.toggleBit(bitsInt, bitIndex, m, n, signed)` -- toggle one bit and
  return the new pattern plus decoded value.
- `QFX.add(a, b, m, n, mode, signed)` -- exact, quantized-operand, and
  double-quantized results.
- `QFX.mul(a, b, m, n, mode, signed)` -- same, with Q(2m).(2n) growth rule.
- `QFX.overflowRamp(value, m, n, signed)` -- wrap vs saturate for an
  out-of-range value.
- `QFX.stepSize(n)`, `QFX.maxError(n)`, `QFX.minValue(m, signed)`,
  `QFX.maxValue(m, n, signed)` -- helpers.

## Notation

Signed Qm.n means 1 sign bit + `m` integer bits + `n` fractional bits, for a
total width of `m + n + 1` bits. So Q7.8/16b is 1 + 7 + 8 bits.

Unsigned Qm.n means `m` integer bits + `n` fractional bits, for a total width
of `m + n` bits.
