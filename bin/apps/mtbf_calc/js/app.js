// app.js -- DOM glue for the Metastability MTBF Calculator. Reads inputs,
// runs MTBF.validate / MTBF.compute, renders results, wires presets.
// No calculation logic lives here; the model owns the math.
var MTBF = (typeof window !== 'undefined' ? window : globalThis).MTBF ||
           ((typeof window !== 'undefined' ? window : globalThis).MTBF = {});

(function (MTBF) {
  'use strict';

  // Input IDs on the page and their model keys.
  var IDS = ['preset', 'c1', 'c2', 'fdata', 'fclk', 'tco', 'tsu', 't0', 'n', 'mission'];
  var MODEL_KEYS = {
    preset: 'preset',
    c1: 'c1',
    c2: 'c2',
    fdata: 'fData',
    fclk: 'fClk',
    tco: 'tCO',
    tsu: 'tSU',
    t0: 't0',
    n: 'n',
    mission: 'missionYears'
  };

  function el(id) { return document.getElementById(id); }

  function readParams() {
    var p = {};
    IDS.forEach(function (id) {
      p[MODEL_KEYS[id]] = el('in-' + id).value;
    });
    return p;
  }

  function setParams(p) {
    if (p.preset !== undefined) { el('in-preset').value = p.preset; }
    if (p.c1 !== undefined) { el('in-c1').value = String(p.c1); }
    if (p.c2 !== undefined) { el('in-c2').value = String(p.c2); }
    if (p.fData !== undefined) { el('in-fdata').value = String(p.fData); }
    if (p.fClk !== undefined) { el('in-fclk').value = String(p.fClk); }
    if (p.tCO !== undefined) { el('in-tco').value = String(p.tCO); }
    if (p.tSU !== undefined) { el('in-tsu').value = String(p.tSU); }
    if (p.t0 !== undefined) { el('in-t0').value = String(p.t0); }
    if (p.n !== undefined) { el('in-n').value = String(p.n); }
    if (p.missionYears !== undefined) { el('in-mission').value = String(p.missionYears); }
  }

  function fmt(x, digits) {
    if (typeof x !== 'number' || !isFinite(x)) { return '-'; }
    if (digits === undefined) { digits = 2; }
    if (Math.abs(x) < 1e-6 || Math.abs(x) >= 1e6) {
      return x.toExponential(digits);
    }
    return x.toFixed(digits);
  }

  function fmtTime(s) {
    var scaled = MTBF.scaleSeconds(s);
    if (typeof scaled.value !== 'number' || !isFinite(scaled.value)) {
      return '-';
    }
    return fmt(scaled.value, 2) + ' ' + scaled.unit;
  }

  function row(label, value, cls) {
    return '<tr' + (cls ? ' class="' + cls + '"' : '') + '><td>' + label +
           '</td><td class="num">' + value + '</td></tr>';
  }

  function renderErrors(errors) {
    IDS.forEach(function (id) {
      var key = MODEL_KEYS[id];
      el('err-' + id).textContent = errors[key] || '';
    });
  }

  function render(r) {
    el('main-result').innerHTML =
      row('Clock period', fmt(r.period, 3) + ' s') +
      row('Per-stage resolution time r', fmt(r.r, 3) + ' s') +
      row('tMET_total for N = ' + r.inputs.n, fmt(r.tMET, 3) + ' s') +
      row('MTBF', fmtTime(r.mtbf));

    var html = '<thead><tr><th>N</th><th>tMET_total (s)</th>' +
               '<th>MTBF</th></tr></thead><tbody>';
    r.table.forEach(function (entry) {
      var cls = entry.n === r.inputs.n ? 'current' : '';
      html += '<tr class="' + cls + '"><td>' + entry.n + '</td>' +
              '<td class="num">' + fmt(entry.tMET, 3) + '</td>' +
              '<td class="num">' + fmtTime(entry.mtbf) + '</td></tr>';
    });
    html += '</tbody>';
    el('mtbf-table').innerHTML = html;

    var verdict;
    if (r.pass) {
      verdict = 'PASS: MTBF ' + fmtTime(r.mtbf) +
        ' <span class="yes">exceeds</span> mission time ' +
        fmt(r.missionYears, 2) + ' years';
      el('banner').className = 'banner pass';
      el('banner').textContent = 'PASS for the stated mission';
    } else {
      verdict = 'FAIL: MTBF ' + fmtTime(r.mtbf) +
        ' <span class="no">is shorter than</span> mission time ' +
        fmt(r.missionYears, 2) + ' years';
      el('banner').className = 'banner';
      el('banner').textContent = 'FAIL for the stated mission';
    }
    el('verdict').innerHTML = verdict;
  }

  function applyPreset(name) {
    var preset = null;
    for (var i = 0; i < MTBF.PRESETS.length; i += 1) {
      if (MTBF.PRESETS[i].name === name) {
        preset = MTBF.PRESETS[i];
        break;
      }
    }
    if (!preset) { return; }
    setParams({
      preset: preset.name,
      c1: preset.c1,
      c2: preset.c2
    });
  }

  function load1GHz() {
    setParams({
      preset: '28 nm (illustrative)',
      c1: 1e-11,
      c2: 1.75e10,
      fData: 1e6,
      fClk: 1e9,
      tCO: 50e-12,
      tSU: 50e-12,
      t0: 10e-12,
      n: 2,
      missionYears: 1
    });
    update();
  }

  function update() {
    var p = readParams();
    var v = MTBF.validate(p);
    renderErrors(v.errors);
    if (!v.ok) {
      el('banner').className = 'banner hidden';
      el('banner').innerHTML = '';
      el('main-result').innerHTML = '';
      el('verdict').innerHTML = '';
      el('mtbf-table').innerHTML = '';
      return;
    }

    // Build a clean numeric bundle from validated strings.
    var clean = {
      preset: p.preset,
      c1: Number(p.c1),
      c2: Number(p.c2),
      fData: Number(p.fData),
      fClk: Number(p.fClk),
      tCO: Number(p.tCO),
      tSU: Number(p.tSU),
      t0: Number(p.t0),
      n: Number(p.n),
      missionYears: Number(p.missionYears)
    };
    render(MTBF.compute(clean));
  }

  MTBF.app = {
    update: update,
    setParams: setParams,
    load1GHz: load1GHz,
    applyPreset: applyPreset
  };
})(MTBF);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = MTBF;
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', function () {
    var IDS = ['preset', 'c1', 'c2', 'fdata', 'fclk', 'tco', 'tsu', 't0', 'n', 'mission'];
    IDS.forEach(function (id) {
      document.getElementById('in-' + id)
        .addEventListener('input', MTBF.app.update);
    });

    document.getElementById('in-preset')
      .addEventListener('change', function () {
        MTBF.app.applyPreset(document.getElementById('in-preset').value);
        MTBF.app.update();
      });

    document.getElementById('btn-1ghz')
      .addEventListener('click', MTBF.app.load1GHz);

    MTBF.app.update();
  });
}
