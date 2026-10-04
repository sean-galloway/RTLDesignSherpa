// app.js -- DOM glue for the CRC Calculator. Reads inputs, runs CRCX.computeCRC,
// renders the checksum, the swapped-convention checksum, and the shift-register
// step table. No calculation logic lives here; the model owns the math.
var CRCX = (typeof window !== 'undefined' ? window : globalThis).CRCX ||
           ((typeof window !== 'undefined' ? window : globalThis).CRCX = {});

(function (CRCX) {
  'use strict';

  function el(id) { return document.getElementById(id); }

  function parseHex(s) {
    if (typeof s !== 'string') { return NaN; }
    s = s.replace(/^0x/i, '').replace(/\s+/g, '');
    if (s === '') { return NaN; }
    var n = parseInt(s, 16);
    return isNaN(n) ? NaN : n;
  }

  function strToBytes(s) {
    var b = [];
    var i;
    for (i = 0; i < s.length; i += 1) {
      b.push(s.charCodeAt(i) & 0xFF);
    }
    return b;
  }

  function parseHexBytes(s) {
    if (typeof s !== 'string') { return {ok: false, error: 'invalid input'}; }
    var tokens = s.split(/[\s,]+/).filter(function (t) { return t !== ''; });
    var bytes = [];
    var i, n;
    for (i = 0; i < tokens.length; i += 1) {
      n = parseHex(tokens[i]);
      if (isNaN(n) || n < 0 || n > 255) {
        return {ok: false, error: 'bad byte "' + tokens[i] + '"'};
      }
      bytes.push(n);
    }
    return {ok: true, bytes: bytes};
  }

  function formatHex(value, width) {
    if (typeof value !== 'number' || !isFinite(value)) { return '-'; }
    var digits = Math.max(2, width / 4);
    var s = value.toString(16).toUpperCase();
    while (s.length < digits) { s = '0' + s; }
    return '0x' + s;
  }

  function formatByte(b) {
    var s = (b & 0xFF).toString(16).toUpperCase();
    return (s.length < 2 ? '0' : '') + s;
  }

  function readParams() {
    var width = Number(el('in-width').value);
    return {
      CRC_POLY: parseHex(el('in-poly').value),
      CRC_INIT: parseHex(el('in-init').value),
      CRC_XOROUT: parseHex(el('in-xorout').value),
      CRC_REFIN: el('in-refin').checked,
      CRC_REFOUT: el('in-refout').checked,
      width: isNaN(width) ? 8 : width
    };
  }

  function readBytes() {
    var fmt = document.querySelector('input[name="in-format"]:checked').value;
    var s = el('in-message').value;
    if (fmt === 'ascii') {
      return {ok: true, bytes: strToBytes(s)};
    }
    return parseHexBytes(s);
  }

  function loadPreset(name) {
    var i, p;
    for (i = 0; i < CRCX.PRESETS.length; i += 1) {
      if (CRCX.PRESETS[i].name === name) {
        p = CRCX.PRESETS[i];
        el('in-poly').value = formatHex(p.params.CRC_POLY, p.params.width);
        el('in-init').value = formatHex(p.params.CRC_INIT, p.params.width);
        el('in-xorout').value = formatHex(p.params.CRC_XOROUT, p.params.width);
        el('in-width').value = String(p.params.width);
        el('in-refin').checked = !!p.params.CRC_REFIN;
        el('in-refout').checked = !!p.params.CRC_REFOUT;
        return;
      }
    }
  }

  function renderShiftTable(perByteSteps, width, poly, refin) {
    el('tap-mask').textContent = formatHex(poly, width);
    el('tap-mask-lsb').textContent = formatHex(CRCX.reflectBits(poly, width), width);

    if (perByteSteps.length === 0) {
      el('shift-table').innerHTML =
        '<p class="hint">No bytes to process. The final value is just the ' +
        'conditioned init register.</p>';
      return;
    }

    var html = '<table class="shift-table"><thead><tr>' +
               '<th>#</th><th>Byte</th><th>Register after byte</th>';
    if (perByteSteps.length <= 4) {
      html += '<th>Per-bit steps (MSB-first bit index)</th>';
    }
    html += '</tr></thead><tbody>';

    perByteSteps.forEach(function (step, idx) {
      html += '<tr><td>' + (idx + 1) + '</td>' +
              '<td class="num">0x' + formatByte(step.byte) + '</td>' +
              '<td class="num">' + formatHex(step.registerAfter, width) + '</td>';
      if (perByteSteps.length <= 4) {
        html += '<td class="bit-cell">';
        step.bitSteps.forEach(function (bs) {
          html += 'b' + bs.bit + ':' + formatHex(bs.registerAfter, width);
          if (bs.xorApplied) {
            html += '<span class="xor-mark">*</span>';
          }
          html += ' ';
        });
        html += '</td>';
      }
      html += '</tr>';
    });
    html += '</tbody></table>';
    el('shift-table').innerHTML = html;
  }

  function update() {
    var params = readParams();
    var bytesRead = readBytes();
    var err = el('err-message');
    err.textContent = '';

    if (!bytesRead.ok) {
      err.textContent = bytesRead.error;
      el('out-result').textContent = '-';
      el('out-other').textContent = '-';
      el('param-summary').textContent = '';
      el('shift-table').innerHTML = '';
      el('tap-mask').textContent = '-';
      el('tap-mask-lsb').textContent = '-';
      return;
    }

    var r = CRCX.computeCRC(params, bytesRead.bytes);
    el('out-result').textContent = formatHex(r.result, params.width);

    var otherParams = {
      CRC_POLY: params.CRC_POLY,
      CRC_INIT: params.CRC_INIT,
      CRC_REFIN: !params.CRC_REFIN,
      CRC_REFOUT: !params.CRC_REFOUT,
      CRC_XOROUT: params.CRC_XOROUT,
      width: params.width
    };
    var other = CRCX.computeCRC(otherParams, bytesRead.bytes);
    el('out-other').textContent = formatHex(other.result, params.width);

    el('param-summary').innerHTML =
      'Width ' + params.width + ', POLY ' + formatHex(params.CRC_POLY, params.width) +
      ', INIT ' + formatHex(params.CRC_INIT, params.width) +
      ', XOROUT ' + formatHex(params.CRC_XOROUT, params.width) +
      ', REFIN ' + (params.CRC_REFIN ? '1' : '0') +
      ', REFOUT ' + (params.CRC_REFOUT ? '1' : '0') +
      ', ' + bytesRead.bytes.length + ' byte' + (bytesRead.bytes.length === 1 ? '' : 's');

    renderShiftTable(r.perByteSteps, params.width, params.CRC_POLY, params.CRC_REFIN);
  }

  function updateHint() {
    var fmt = document.querySelector('input[name="in-format"]:checked').value;
    el('hint-format').textContent = fmt === 'ascii'
      ? 'Plain ASCII text (each byte = one character).'
      : 'Space or comma separated bytes, e.g. "0x31 0x32" or "31,32".';
  }

  CRCX.app = {
    update: update,
    updateHint: updateHint,
    loadPreset: loadPreset,
    formatHex: formatHex
  };
})(CRCX);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = CRCX;
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', function () {
    var CRCX = (typeof window !== 'undefined' ? window : globalThis).CRCX;
    var textInputs = ['in-poly', 'in-init', 'in-xorout', 'in-message'];
    textInputs.forEach(function (id) {
      document.getElementById(id).addEventListener('input', CRCX.app.update);
    });
    var changeInputs = ['in-width', 'in-refin', 'in-refout'];
    changeInputs.forEach(function (id) {
      document.getElementById(id).addEventListener('change', CRCX.app.update);
    });
    document.getElementById('in-preset').addEventListener('change', function () {
      CRCX.app.loadPreset(this.value);
      CRCX.app.update();
    });
    var radios = document.querySelectorAll('input[name="in-format"]');
    var i;
    for (i = 0; i < radios.length; i += 1) {
      radios[i].addEventListener('change', function () {
        CRCX.app.updateHint();
        CRCX.app.update();
      });
    }
    CRCX.app.loadPreset('CRC-8');
    CRCX.app.updateHint();
    CRCX.app.update();
  });
}
