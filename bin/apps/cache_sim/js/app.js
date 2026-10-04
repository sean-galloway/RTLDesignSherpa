// js/app.js -- DOM glue for cache_sim. Reads controls, calls model.js,
// renders results, wires generators and the guided example.
var CACHESIM = (typeof window !== 'undefined' ? window : globalThis).CACHESIM ||
               ((typeof window !== 'undefined' ? window : globalThis).CACHESIM = {});

(function (CS) {
  'use strict';

  var IDS = {
    sets: 'in-sets',
    ways: 'in-ways',
    block: 'in-block',
    policy: 'in-policy',
    seed: 'in-seed',
    trace: 'in-trace'
  };

  function el(id) { return document.getElementById(id); }

  function numberOrSelf(x) {
    if (typeof x === 'string' && x.trim() !== '') { return Number(x); }
    return x;
  }

  function ilog2(x) {
    x = x >>> 0;
    var n = 0;
    while (x > 1) { x = x >>> 1; n += 1; }
    return n;
  }

  function setsFromExp(exp) { return 1 << ((numberOrSelf(exp) >>> 0)); }
  function blockFromExp(exp) { return 1 << ((numberOrSelf(exp) >>> 0)); }
  function setsExpForValue(v) { return ilog2(v); }
  function blockExpForValue(v) { return ilog2(v); }

  function esc(s) {
    return String(s)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;');
  }

  function fmtHex(x) {
    if (x === null || x === undefined) { return '-'; }
    return '0x' + (x >>> 0).toString(16).toUpperCase();
  }

  function fmtPct(r) {
    if (typeof r !== 'number' || isNaN(r)) { return '-'; }
    return (r * 100).toFixed(1);
  }

  function getConfig() {
    return {
      sets: setsFromExp(el(IDS.sets).value),
      ways: (numberOrSelf(el(IDS.ways).value) >>> 0),
      blockSize: blockFromExp(el(IDS.block).value),
      policy: el(IDS.policy).value.toUpperCase(),
      seed: numberOrSelf(el(IDS.seed).value)
    };
  }

  function setConfig(c) {
    el(IDS.sets).value = setsExpForValue(c.sets);
    el(IDS.ways).value = c.ways;
    el(IDS.block).value = blockExpForValue(c.blockSize);
    el(IDS.policy).value = c.policy;
    el(IDS.seed).value = c.seed;
    updateSliderLabels();
  }

  function getTrace() {
    return CS.parseAddressText(el(IDS.trace).value);
  }

  function setTrace(addresses) {
    var lines = [];
    for (var i = 0; i < addresses.length; i += 1) {
      lines.push(fmtHex(addresses[i]).toLowerCase());
    }
    el(IDS.trace).value = lines.join('\n');
  }

  function updateSliderLabels() {
    el('val-sets').textContent = String(setsFromExp(el(IDS.sets).value));
    el('val-ways').textContent = String(el(IDS.ways).value);
    el('val-block').textContent = String(blockFromExp(el(IDS.block).value));
  }

  function renderErrors(configErrs, traceMsg) {
    ['sets', 'ways', 'block', 'policy', 'trace'].forEach(function (id) {
      var span = el('err-' + id);
      if (span) { span.textContent = ''; }
    });
    for (var k in configErrs) {
      if (configErrs.hasOwnProperty(k)) {
        var spanId = k === 'blockSize' ? 'err-block' : 'err-' + k;
        var span = el(spanId);
        if (span) { span.textContent = configErrs[k]; }
      }
    }
    if (traceMsg) {
      el('err-trace').textContent = traceMsg;
    }
  }

  function clearResults() {
    el('hit-rate').textContent = '-';
    el('totals').innerHTML = '';
    el('access-log').innerHTML = '';
    el('occupancy').innerHTML = '';
    el('comparison').innerHTML = '';
    el('banner').className = 'banner hidden';
    el('banner').textContent = '';
  }

  function row2(label, value) {
    return '<tr><td>' + esc(label) + '</td><td class="num">' + esc(String(value)) + '</td></tr>';
  }

  function renderTotals(totals) {
    var rows = '';
    rows += row2('Accesses', totals.hits + totals.misses);
    rows += row2('Hits', totals.hits);
    rows += row2('Misses', totals.misses);
    rows += row2('Compulsory misses', totals.compulsory);
    rows += row2('Capacity misses', totals.capacity);
    rows += row2('Conflict misses', totals.conflict);
    el('totals').innerHTML = rows;
  }

  function renderAccessLog(perAccess) {
    var html = '<thead><tr><th>#</th><th>Address</th><th>Set</th><th>Way</th><th>Result</th></tr></thead><tbody>';
    for (var i = 0; i < perAccess.length; i += 1) {
      var a = perAccess[i];
      var cls = a.hit ? 'hit' : ('miss ' + a.missClass);
      html += '<tr class="' + cls + '"><td class="num">' + (i + 1) + '</td>' +
              '<td class="num">' + fmtHex(a.addr).toLowerCase() + '</td>' +
              '<td class="num">' + a.setIndex + '</td>' +
              '<td class="num">' + a.way + '</td>' +
              '<td>' + (a.hit ? 'H' : 'M') + ' ' + a.missClass + '</td></tr>';
    }
    html += '</tbody>';
    el('access-log').innerHTML = html;
  }

  function renderOccupancy(occupancy) {
    if (!occupancy || occupancy.length === 0) { return; }
    var html = '<thead><tr><th>Set</th>';
    for (var w = 0; w < occupancy[0].length; w += 1) {
      html += '<th>Way ' + w + '</th>';
    }
    html += '</tr></thead><tbody>';
    for (var s = 0; s < occupancy.length; s += 1) {
      html += '<tr><td class="num">' + s + '</td>';
      for (var w = 0; w < occupancy[s].length; w += 1) {
        html += '<td class="num">' + fmtHex(occupancy[s][w]).toLowerCase() + '</td>';
      }
      html += '</tr>';
    }
    html += '</tbody>';
    el('occupancy').innerHTML = html;
  }

  function render(result) {
    renderErrors({}, '');
    el('hit-rate').textContent = fmtPct(result.totals.hitRate);
    renderTotals(result.totals);
    renderAccessLog(result.perAccess);
    renderOccupancy(result.occupancy);
  }

  function showBanner(msg) {
    el('banner').textContent = msg;
    el('banner').className = 'banner';
  }

  function run() {
    var c = getConfig();
    var cv = CS.validateConfig(c);
    var addresses = getTrace();
    var traceMsg = '';
    for (var i = 0; i < addresses.length; i += 1) {
      if (isNaN(addresses[i])) {
        traceMsg = 'trace line ' + (i + 1) + ' is not a valid address';
        break;
      }
    }
    renderErrors(cv.errors, traceMsg);
    if (!cv.ok || traceMsg) {
      clearResults();
      if (traceMsg) { showBanner(traceMsg); }
      return;
    }
    try {
      var result = CS.simulate(c, addresses, c.seed);
      render(result);
    } catch (e) {
      showBanner(e.message);
      clearResults();
    }
  }

  function generateAndRun(fn) {
    return function () {
      var seed = numberOrSelf(el(IDS.seed).value);
      var addresses = fn(seed);
      setTrace(addresses);
      run();
    };
  }

  function renderCompareCard(title, cfg, result) {
    return '<div class="compare-card">' +
      '<h4>' + esc(title) + '</h4>' +
      '<p>' + esc(cfg.sets + ' sets x ' + cfg.ways + ' ways, block ' + cfg.blockSize + ' word(s), ' + cfg.policy) + '</p>' +
      '<table class="results"><tbody>' +
      row2('Hit rate', fmtPct(result.totals.hitRate) + '%') +
      row2('Hits', result.totals.hits) +
      row2('Misses', result.totals.misses) +
      row2('Conflict misses', result.totals.conflict) +
      row2('Capacity misses', result.totals.capacity) +
      '</tbody></table></div>';
  }

  function runComparison(trace, cfgA, cfgB) {
    setTrace(trace);
    var rA = CS.simulate(cfgA, trace, cfgA.seed || 1);
    var rB = CS.simulate(cfgB, trace, cfgB.seed || 1);
    var html = '<div class="compare-grid">' +
      renderCompareCard('Direct-mapped', cfgA, rA) +
      renderCompareCard('2-way set-associative', cfgB, rB) +
      '</div>';
    el('comparison').innerHTML = html;
  }

  function wire() {
    [IDS.sets, IDS.ways, IDS.block, IDS.policy, IDS.seed].forEach(function (id) {
      var node = el(id);
      if (node) {
        node.addEventListener('input', function () {
          updateSliderLabels();
          run();
        });
      }
    });
    if (el(IDS.trace)) {
      el(IDS.trace).addEventListener('input', run);
    }

    if (el('btn-seq')) {
      el('btn-seq').addEventListener('click', generateAndRun(function (seed) {
        return CS.generateSequential(
          numberOrSelf(el('gen-seq-len').value),
          numberOrSelf(el('gen-seq-start').value)
        );
      }));
    }
    if (el('btn-str')) {
      el('btn-str').addEventListener('click', generateAndRun(function (seed) {
        return CS.generateStrided(
          numberOrSelf(el('gen-str-len').value),
          numberOrSelf(el('gen-str-start').value),
          numberOrSelf(el('gen-str-stride').value)
        );
      }));
    }
    if (el('btn-rand')) {
      el('btn-rand').addEventListener('click', generateAndRun(function (seed) {
        return CS.generateRandom(
          numberOrSelf(el('gen-rand-len').value),
          seed,
          numberOrSelf(el('gen-rand-max').value)
        );
      }));
    }
    if (el('btn-example')) {
      el('btn-example').addEventListener('click', function () {
        var trace = [0, 2, 0, 2, 0];
        var cfgA = { sets: 2, ways: 1, blockSize: 1, policy: 'LRU', seed: 1 };
        var cfgB = { sets: 2, ways: 2, blockSize: 1, policy: 'LRU', seed: 1 };
        setConfig(cfgA);
        runComparison(trace, cfgA, cfgB);
        run();
      });
    }
  }

  CS.app = {
    run: run,
    setConfig: setConfig,
    setTrace: setTrace,
    runComparison: runComparison,
    esc: esc,
    fmtHex: fmtHex
  };

  if (typeof document !== 'undefined') {
    function boot() {
      if (el(IDS.sets)) {
        wire();
        updateSliderLabels();
        run();
      }
    }
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', boot);
    } else {
      boot();
    }
  }
})(CACHESIM);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = CACHESIM;
}
