// app.js -- DOM glue for the FIFO Depth Calculator. Reads the six inputs,
// runs FD.validate / FD.compute, renders results, wires the example table.
// No calculation logic lives here; the model owns the math.
var FD = (typeof window !== 'undefined' ? window : globalThis).FD ||
         ((typeof window !== 'undefined' ? window : globalThis).FD = {});

(function (FD) {
  'use strict';

  var IDS = ['fA', 'fB', 'burst', 'widle', 'ridle', 'nsync'];
  var MODEL_KEYS = {
    fA: 'fA', fB: 'fB', burst: 'burst', widle: 'wIdle', ridle: 'rIdle', nsync: 'nSync'
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
    el('in-fA').value = p.fA;
    el('in-fB').value = p.fB;
    el('in-burst').value = p.burst;
    el('in-widle').value = p.wIdle;
    el('in-ridle').value = p.rIdle;
    el('in-nsync').value = p.nSync;
  }

  function fmt(x, digits) {
    if (typeof x !== 'number' || !isFinite(x)) { return '-'; }
    if (Math.abs(x - Math.round(x)) < 1e-9) { return String(Math.round(x)); }
    return x.toFixed(digits === undefined ? 1 : digits);
  }

  // HTML-escape text destined for markup (attribute values, innerHTML).
  function esc(s) {
    return String(s)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;');
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
    el('chain').innerHTML =
      row('Write time per item (ns)', fmt(r.writeNsPerItem, 3)) +
      row('Total write time (ns)', fmt(r.writeNsTotal, 1)) +
      row('Read time per item (ns)', fmt(r.readNsPerItem, 3)) +
      row('Items read in write period', r.itemsRead) +
      row('Raw depth (burst - reads)', r.rawDepth);

    var s = r.steady;
    var verdict;
    if (s.drainable) {
      verdict = 'Steady-state: write rate ' + fmt(s.writeRate, 2) +
        ' &lt;= read rate ' + fmt(s.readRate, 2) +
        ' Mwords/s &mdash; <span class="yes">YES (drainable)</span>';
      el('banner').className = 'banner hidden';
      el('banner').innerHTML = '';
    } else {
      verdict = 'Steady-state: write rate ' + fmt(s.writeRate, 2) +
        ' &gt; read rate ' + fmt(s.readRate, 2) + ' Mwords/s &mdash; ' +
        '<span class="no">NO</span>';
      el('banner').className = 'banner';
      el('banner').textContent =
        'NO - bursts grow without bound, need flow control';
    }
    el('verdict').innerHTML = verdict;

    el('depths').innerHTML =
      row('Raw depth (formula)', r.rawDepth) +
      row('+ Sync margin (N_FLOP_CROSS)', r.totalDepth - r.rawDepth) +
      row('Total depth needed', r.totalDepth, 'total') +
      row('Gray depth (USE_JOHNSON=0, power of 2)', r.grayDepth) +
      row('Johnson depth (USE_JOHNSON=1, even)', r.johnsonDepth) +
      row('Johnson savings vs Gray (slots)', r.savingsSlots) +
      row('Johnson savings vs Gray (%)', fmt(r.savingsPct * 100, 1) + '%');
  }

  function renderExamples() {
    var html = '<table><thead><tr>' +
      '<th>Case</th><th>fA</th><th>fB</th><th>Burst</th><th>W_Idle</th>' +
      '<th>R_Idle</th><th>N_Sync</th></tr></thead><tbody>';
    FD.EXAMPLES.forEach(function (ex, i) {
      html += '<tr data-i="' + i + '" title="' + esc(ex.note) + '">' +
        '<td>' + ex.case + '</td><td>' + ex.fA + '</td><td>' + ex.fB + '</td>' +
        '<td>' + ex.burst + '</td><td>' + ex.wIdle + '</td><td>' + ex.rIdle +
        '</td><td>' + ex.nSync + '</td></tr>';
    });
    html += '</tbody></table>';
    el('examples').innerHTML = html;

    Array.prototype.forEach.call(
      el('examples').querySelectorAll('tbody tr'),
      function (tr) {
        tr.addEventListener('click', function () {
          var ex = FD.EXAMPLES[Number(tr.getAttribute('data-i'))];
          setParams(ex);
          update();
        });
      }
    );
  }

  function update() {
    var p = readParams();
    var v = FD.validate(p);
    renderErrors(v.errors);
    if (!v.ok) {
      el('banner').className = 'banner hidden';
      el('banner').innerHTML = '';
      el('chain').innerHTML = '';
      el('verdict').innerHTML = '';
      el('depths').innerHTML = '';
      return;
    }
    render(FD.compute({
      fA: Number(p.fA), fB: Number(p.fB), burst: Number(p.burst),
      wIdle: Number(p.wIdle), rIdle: Number(p.rIdle), nSync: Number(p.nSync)
    }));
  }

  FD.app = {
    update: update,
    renderExamples: renderExamples,
    setParams: setParams,
    esc: esc
  };
})(FD);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = FD;
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', function () {
    var IDS = ['fA', 'fB', 'burst', 'widle', 'ridle', 'nsync'];
    IDS.forEach(function (id) {
      document.getElementById('in-' + id)
        .addEventListener('input', FD.app.update);
    });
    FD.app.renderExamples();
    FD.app.update();
  });
}
