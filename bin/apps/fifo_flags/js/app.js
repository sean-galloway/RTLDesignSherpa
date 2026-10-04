// app.js -- DOM glue for the FIFO Flags Calculator. Reads the five inputs,
// runs FIFOFLAGS.validate / FIFOFLAGS.compute, renders results, wires the
// example table. No calculation logic lives here; the model owns the math.
var FIFOFLAGS = (typeof window !== 'undefined' ? window : globalThis).FIFOFLAGS || ((typeof window !== 'undefined' ? window : globalThis).FIFOFLAGS = {});

(function (FF) {
  'use strict';

  var IDS = ['depth', 'fwr', 'frd', 'nsync', 'bubble'];
  var MODEL_KEYS = {
    depth: 'depth', fwr: 'fWr', frd: 'fRd', nsync: 'nSync', bubble: 'bubblePct'
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
    el('in-depth').value = p.depth;
    el('in-fwr').value = p.fWr;
    el('in-frd').value = p.fRd;
    el('in-nsync').value = p.nSync;
    el('in-bubble').value = p.bubblePct;
  }

  function fmt(x) {
    if (typeof x !== 'number' || !isFinite(x)) { return '-'; }
    if (Math.abs(x - Math.round(x)) < 1e-9) { return String(Math.round(x)); }
    return x.toFixed(2);
  }

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
    el('flags').innerHTML =
      row('FIFO depth', r.depth) +
      row('AF margin (write-side uncertainty)', r.marginAF) +
      row('AE margin (read-side uncertainty)', r.marginAE) +
      row('Bubble items (each end)', r.bubbleItems) +
      row('Almost-full threshold', r.afThreshold, 'total') +
      row('Almost-empty threshold', r.aeThreshold, 'total');

    if (r.pass) {
      el('banner').className = 'banner good';
      el('banner').textContent = r.message;
      el('verdict').innerHTML = '<span class="yes">PASS</span> &mdash; thresholds are separated';
    } else {
      el('banner').className = 'banner';
      el('banner').textContent = r.message;
      el('verdict').innerHTML = '<span class="no">FAIL</span> &mdash; AF must be greater than AE';
    }
  }

  function renderExamples() {
    var html = '<table><thead><tr>' +
      '<th>Case</th><th>Depth</th><th>f_wr</th><th>f_rd</th><th>N</th>' +
      '<th>Bubble%</th></tr></thead><tbody>';
    FF.EXAMPLES.forEach(function (ex, i) {
      html += '<tr data-i="' + i + '" title="' + esc(ex.note) + '">' +
        '<td>' + ex.case + '</td><td>' + ex.depth + '</td><td>' + ex.fWr + '</td>' +
        '<td>' + ex.fRd + '</td><td>' + ex.nSync + '</td><td>' + ex.bubblePct +
        '</td></tr>';
    });
    html += '</tbody></table>';
    el('examples').innerHTML = html;

    Array.prototype.forEach.call(
      el('examples').querySelectorAll('tbody tr'),
      function (tr) {
        tr.addEventListener('click', function () {
          var ex = FF.EXAMPLES[Number(tr.getAttribute('data-i'))];
          setParams(ex);
          update();
        });
      }
    );
  }

  function update() {
    var p = readParams();
    var v = FF.validate(p);
    renderErrors(v.errors);
    if (!v.ok) {
      el('banner').className = 'banner hidden';
      el('banner').innerHTML = '';
      el('flags').innerHTML = '';
      el('verdict').innerHTML = '';
      return;
    }
    render(FF.compute({
      depth: Number(p.depth), fWr: Number(p.fWr), fRd: Number(p.fRd),
      nSync: Number(p.nSync), bubblePct: Number(p.bubblePct)
    }));
  }

  FF.app = {
    update: update,
    renderExamples: renderExamples,
    setParams: setParams,
    esc: esc
  };
})(FIFOFLAGS);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = FIFOFLAGS;
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', function () {
    var IDS = ['depth', 'fwr', 'frd', 'nsync', 'bubble'];
    IDS.forEach(function (id) {
      document.getElementById('in-' + id)
        .addEventListener('input', FF.app.update);
    });
    FF.app.renderExamples();
    FF.app.update();
  });
}
