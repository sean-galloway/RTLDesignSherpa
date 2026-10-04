// app.js -- DOM glue for the Slack Explorer. Reads the inputs, keeps range
// and number controls in sync, runs SLACK.validate / SLACK.compute, and
// renders the slack and pipeline panels. No calculation logic lives here.
var SLACK = (typeof window !== 'undefined' ? window : globalThis).SLACK ||
            ((typeof window !== 'undefined' ? window : globalThis).SLACK = {});

(function (SLACK) {
  'use strict';

  var IDS = ['T', 'tCO', 'tLOGIC', 'tROUTE', 'skew', 'tSU', 'tHD', 'K'];

  function el(id) { return document.getElementById(id); }

  function readParams() {
    var p = {};
    IDS.forEach(function (id) {
      p[id] = el('in-' + id).value;
    });
    return p;
  }

  function setParams(p) {
    IDS.forEach(function (id) {
      el('in-' + id).value = p[id];
      var range = el('in-' + id + '-range');
      if (range) { range.value = p[id]; }
    });
  }

  function fmt(x, digits) {
    if (typeof x !== 'number' || !isFinite(x)) { return '-'; }
    if (Math.abs(x - Math.round(x)) < 1e-9) { return String(Math.round(x)); }
    return x.toFixed(digits === undefined ? 2 : digits);
  }

  function passFailCell(pass) {
    return '<td class="' + (pass ? 'pass' : 'fail') + '">' +
           (pass ? 'PASS' : 'FAIL') + '</td>';
  }

  function row(label, value, cls) {
    return '<tr' + (cls ? ' class="' + cls + '"' : '') + '><td>' + label +
           '</td><td class="num">' + value + '</td></tr>';
  }

  function renderErrors(errors) {
    IDS.forEach(function (id) {
      el('err-' + id).textContent = errors[id] || '';
    });
  }

  function slackRow(label, value, pass) {
    return '<tr><td>' + label + '</td><td class="num">' + value + '</td>' +
           passFailCell(pass) + '</tr>';
  }

  function renderSlack(s) {
    var banner = el('slack-banner');
    if (s.pass) {
      banner.className = 'banner good';
      banner.textContent = 'PASS - both setup and hold margins are positive';
    } else {
      banner.className = 'banner';
      banner.textContent = 'FAIL - see below';
    }

    el('slack-results').innerHTML =
      slackRow('Setup Slack (ns)', fmt(s.setupSlack, 3), s.setupPass) +
      slackRow('Hold Slack (ns)', fmt(s.holdSlack, 3), s.holdPass);

    el('slack-hint').textContent = s.hint;
  }

  function renderPipeline(pipeline) {
    var selected = pipeline.selected;
    el('pipeline-takeaway').innerHTML =
      'K = ' + selected.K + ' stages: ' +
      fmt(selected.maxFreq, 1) + ' MHz max, ' +
      selected.latency + '-cycle latency' +
      (selected.closesWithT ? ' (closes with current T)' :
       ' (does NOT close with current T)') + '.';

    var html = '<thead><tr>' +
      '<th>K</th><th>Stage Logic (ns)</th><th>Min Period (ns)</th>' +
      '<th>Max Freq (MHz)</th><th>Latency (cycles)</th><th>Closes?</th>' +
      '</tr></thead><tbody>';
    pipeline.table.forEach(function (r) {
      html += '<tr class="' + (r.closesWithT ? 'closing' : 'not-closing') + '">' +
        '<td class="num">' + r.K + '</td>' +
        '<td class="num">' + fmt(r.stageLogic, 3) + '</td>' +
        '<td class="num">' + fmt(r.minPeriod, 3) + '</td>' +
        '<td class="num">' + fmt(r.maxFreq, 1) + '</td>' +
        '<td class="num">' + r.latency + '</td>' +
        '<td class="num">' + (r.closesWithT ? 'YES' : 'NO') + '</td>' +
        '</tr>';
    });
    html += '</tbody>';
    el('pipeline-table').innerHTML = html;
  }

  function update() {
    var p = readParams();
    var v = SLACK.validate(p);
    renderErrors(v.errors);
    if (!v.ok) {
      el('slack-banner').className = 'banner hidden';
      el('slack-banner').innerHTML = '';
      el('slack-results').innerHTML = '';
      el('slack-hint').innerHTML = '';
      el('pipeline-takeaway').innerHTML = '';
      el('pipeline-table').innerHTML = '';
      return;
    }
    var numeric = {};
    IDS.forEach(function (id) { numeric[id] = Number(p[id]); });
    var r = SLACK.compute(numeric);
    renderSlack(r.slack);
    renderPipeline(r.pipeline);
  }

  function syncFromRange(id) {
    el('in-' + id).value = el('in-' + id + '-range').value;
    update();
  }

  function syncFromNumber(id) {
    var range = el('in-' + id + '-range');
    if (range) { range.value = el('in-' + id).value; }
    update();
  }

  SLACK.app = {
    update: update,
    setParams: setParams,
    syncFromRange: syncFromRange,
    syncFromNumber: syncFromNumber
  };
})(SLACK);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = SLACK;
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', function () {
    var IDS = ['T', 'tCO', 'tLOGIC', 'tROUTE', 'skew', 'tSU', 'tHD', 'K'];
    IDS.forEach(function (id) {
      var range = document.getElementById('in-' + id + '-range');
      var num = document.getElementById('in-' + id);
      if (range) {
        range.addEventListener('input', function () {
          SLACK.app.syncFromRange(id);
        });
      }
      num.addEventListener('input', function () {
        SLACK.app.syncFromNumber(id);
      });
    });
    SLACK.app.update();
  });
}
