// app.js -- DOM glue for the Q-Format Explorer. Reads inputs, runs
// QFX model functions, and renders results. No calculation logic here.
var QFX = (typeof window !== 'undefined' ? window : globalThis).QFX ||
          ((typeof window !== 'undefined' ? window : globalThis).QFX = {});

(function (QFX) {
  'use strict';

  function el(id) { return document.getElementById(id); }

  function fmt(x, digits) {
    if (typeof x !== 'number' || !isFinite(x)) { return '-'; }
    if (Math.abs(x - Math.round(x)) < 1e-12) { return String(Math.round(x)); }
    return x.toFixed(digits === undefined ? 6 : digits);
  }

  function fmtExp(x) {
    if (typeof x !== 'number' || !isFinite(x)) { return '-'; }
    if (x === 0) { return '0'; }
    var a = Math.abs(x);
    if (a < 1e-4 || a >= 1e6) { return x.toExponential(4); }
    return fmt(x, 6);
  }

  function esc(s) {
    return String(s)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;');
  }

  function parseIntStrict(s) {
    var n = Number(String(s).trim());
    return (isFinite(n) && n === Math.floor(n) && n >= 0) ? n : NaN;
  }

  function parseReal(s) {
    return Number(String(s).trim());
  }

  function parseBits(s) {
    var t = String(s).trim();
    var n;
    if (/^0x[0-9a-fA-F]+$/i.test(t)) {
      n = parseInt(t, 16);
    } else {
      n = Number(t);
    }
    return (isFinite(n) && n === Math.floor(n) && n >= 0) ? n : NaN;
  }

  function readConfig() {
    var m = parseIntStrict(el('in-m').value);
    var n = parseIntStrict(el('in-n').value);
    var mode = el('in-mode').value;
    var signed = el('in-signed').value === 'signed';
    return { m: m, n: n, mode: mode, signed: signed };
  }

  function isConfigValid(cfg) {
    return isFinite(cfg.m) && isFinite(cfg.n) &&
           QFX.validate(cfg.m, cfg.n, cfg.signed).ok;
  }

  function renderConfigErrors(cfg) {
    var v = QFX.validate(cfg.m, cfg.n, cfg.signed);
    el('err-m').textContent = (isFinite(cfg.m) && v.errors.length > 0) ? v.errors[0] : '';
    el('err-n').textContent = '';
  }

  function renderRange(cfg) {
    if (!isConfigValid(cfg)) {
      el('out-range').textContent = '';
      return;
    }
    var c = QFX.config(cfg.m, cfg.n, cfg.signed);
    el('out-range').textContent =
      (cfg.signed ? 'Signed' : 'Unsigned') + ' | width ' + c.totalBits +
      ' bits | range [' + fmtExp(c.min) + ', ' + fmtExp(c.max) +
      '] | step ' + fmtExp(c.step);
  }

  function renderBinaryLabels(cfg) {
    if (!isConfigValid(cfg)) {
      el('out-labels').textContent = '';
      return;
    }
    var s = cfg.signed ? 'S' : 'i';
    var i = cfg.signed ? 1 : 0;
    while (i < cfg.m || (cfg.signed && i <= cfg.m)) {
      s += ' i';
      i += 1;
    }
    s += ' .';
    i = 1;
    while (i <= cfg.n) { s += ' f'; i += 1; }
    el('out-labels').textContent = s;
  }

  function bitSpan(idx, bitsInt) {
    var bit = (bitsInt & Math.pow(2, idx)) !== 0 ? '1' : '0';
    return '<span class="bit" data-idx="' + idx + '">' + bit + '</span>';
  }

  // Render the bit pattern as clickable spans. bitIndex 0 is the LSB.
  function renderClickableBits(bitsInt, cfg) {
    var c = QFX.config(cfg.m, cfg.n, cfg.signed);
    if (!c.ok) { return esc('-'); }
    var bits = c.totalBits;
    var s = '';
    var idx = bits - 1;

    if (cfg.signed) {
      s += bitSpan(idx, bitsInt);
      idx -= 1;
      s += '<span class="separator"> </span>';
    }

    var i;
    for (i = 0; i < cfg.m; i += 1) {
      s += bitSpan(idx, bitsInt);
      idx -= 1;
    }

    s += '<span class="separator"> .</span>';

    for (i = 0; i < cfg.n; i += 1) {
      s += bitSpan(idx, bitsInt);
      idx -= 1;
    }

    return s;
  }

  function updateFromReal() {
    var cfg = readConfig();
    if (!isConfigValid(cfg)) { return; }

    var real = parseReal(el('in-real').value);
    if (!isFinite(real)) { return; }

    var r = QFX.valueToFixed(real, cfg.m, cfg.n, cfg.mode, cfg.signed);
    el('in-bits').value = '0x' + r.bitsInt.toString(16).toUpperCase();
    renderConverter(r, real);
  }

  function updateFromBits() {
    var cfg = readConfig();
    if (!isConfigValid(cfg)) { return; }

    var bits = parseBits(el('in-bits').value);
    if (!isFinite(bits)) { return; }

    var r = QFX.fixedToValue(bits, cfg.m, cfg.n, cfg.signed);
    el('in-real').value = String(r.value);
    renderConverter(r, r.value);
  }

  function renderConverter(r, real) {
    el('out-binary').innerHTML = renderClickableBits(r.bitsInt, r);
    wireBitClicks();
    el('out-represented').textContent = fmtExp(r.value);
    el('out-error').textContent = fmtExp(Math.abs(real - r.value));
    el('out-max-error').textContent = fmtExp(r.maxError);
    el('out-step').textContent = fmtExp(r.step);
    renderBinaryLabels(r);
  }

  function wireBitClicks() {
    var node = el('out-binary');
    if (!node) { return; }
    Array.prototype.forEach.call(node.querySelectorAll('.bit'), function (span) {
      span.addEventListener('click', function () {
        var idx = Number(span.getAttribute('data-idx'));
        toggleBit(idx);
      });
    });
  }

  function toggleBit(bitIndex) {
    var cfg = readConfig();
    if (!isConfigValid(cfg)) { return; }

    var bits = parseBits(el('in-bits').value);
    if (!isFinite(bits)) { return; }

    var t = QFX.toggleBit(bits, bitIndex, cfg.m, cfg.n, cfg.signed);
    if (!t.ok) { return; }

    el('in-bits').value = '0x' + t.newBits.toString(16).toUpperCase();
    var r = QFX.fixedToValue(t.newBits, cfg.m, cfg.n, cfg.signed);
    el('in-real').value = String(r.value);
    renderConverter(r, r.value);
  }

  function renderArithmetic() {
    var cfg = readConfig();
    if (!isConfigValid(cfg)) {
      el('out-arith-rule').textContent = '';
      el('out-a-value').textContent = '-';
      el('out-a-bits').textContent = '-';
      el('out-b-value').textContent = '-';
      el('out-b-bits').textContent = '-';
      el('out-exact').textContent = '-';
      el('out-quantized').textContent = '-';
      el('out-result-value').textContent = '-';
      el('out-result-bits').textContent = '-';
      return;
    }

    var a = parseReal(el('in-a').value);
    var b = parseReal(el('in-b').value);
    var op = el('in-op').value;
    var r;

    if (!isFinite(a) || !isFinite(b)) { return; }

    if (op === 'mul') {
      r = QFX.mul(a, b, cfg.m, cfg.n, cfg.mode, cfg.signed);
    } else {
      r = QFX.add(a, b, cfg.m, cfg.n, cfg.mode, cfg.signed);
    }

    el('out-arith-rule').textContent = r.growthRule;
    el('out-a-value').textContent = fmtExp(r.aFixed.value);
    el('out-a-bits').textContent = r.aFixed.bitsStr;
    el('out-b-value').textContent = fmtExp(r.bFixed.value);
    el('out-b-bits').textContent = r.bFixed.bitsStr;
    el('out-exact').textContent = fmtExp(r.exact);
    el('out-quantized').textContent = fmtExp(r.quantized);
    el('out-result-value').textContent = fmtExp(r.result.value) +
      (r.result.overflow ? ' (overflow)' : '');
    el('out-result-bits').textContent = r.result.bitsStr;
  }

  function renderRamp() {
    var cfg = readConfig();
    if (!isConfigValid(cfg)) {
      el('out-wrap-binary').textContent = '-';
      el('out-wrap-value').textContent = '-';
      el('out-sat-binary').textContent = '-';
      el('out-sat-value').textContent = '-';
      return;
    }

    var value = parseReal(el('in-ramp').value);
    if (!isFinite(value)) { return; }

    var ramp = QFX.overflowRamp(value, cfg.m, cfg.n, cfg.signed);
    el('out-wrap-binary').textContent = ramp.wrap.bitsStr;
    el('out-wrap-value').textContent = fmtExp(ramp.wrap.value);
    el('out-sat-binary').textContent = ramp.saturate.bitsStr;
    el('out-sat-value').textContent = fmtExp(ramp.saturate.value);
  }

  function updatePreset() {
    var val = el('in-preset').value;
    if (val === 'custom') { return; }
    var parts = val.split(',');
    el('in-m').value = parts[0];
    el('in-n').value = parts[1];
    update();
  }

  function update() {
    var cfg = readConfig();
    renderConfigErrors(cfg);
    renderRange(cfg);

    if (!isConfigValid(cfg)) {
      el('out-binary').textContent = '-';
      el('out-labels').textContent = '';
      el('out-represented').textContent = '-';
      el('out-error').textContent = '-';
      el('out-max-error').textContent = '-';
      el('out-step').textContent = '-';
      renderArithmetic();
      renderRamp();
      return;
    }

    updateFromReal();
    renderArithmetic();
    renderRamp();
  }

  QFX.app = {
    update: update,
    updateFromReal: updateFromReal,
    updateFromBits: updateFromBits,
    renderArithmetic: renderArithmetic,
    renderRamp: renderRamp,
    updatePreset: updatePreset,
    toggleBit: toggleBit,
    esc: esc
  };
})(QFX);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = QFX;
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', function () {
    var preset = document.getElementById('in-preset');
    if (preset) { preset.addEventListener('change', QFX.app.updatePreset); }

    ['m', 'n', 'mode', 'signed'].forEach(function (id) {
      var node = document.getElementById('in-' + id);
      if (node) { node.addEventListener('input', QFX.app.update); }
    });

    document.getElementById('in-real')
      .addEventListener('input', QFX.app.updateFromReal);
    document.getElementById('in-bits')
      .addEventListener('input', QFX.app.updateFromBits);
    ['a', 'b', 'op'].forEach(function (id) {
      document.getElementById('in-' + id)
        .addEventListener('input', QFX.app.renderArithmetic);
    });
    document.getElementById('in-ramp')
      .addEventListener('input', QFX.app.renderRamp);

    QFX.app.update();
  });
}
