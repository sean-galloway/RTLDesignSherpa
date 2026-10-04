// app.js -- DOM glue for the CDC drill. Reads the mode/tier filters, builds
// a session from the model, renders questions, and wires the answer UI.
// No scenario logic lives here; the model and content modules own that.
var CDCD = (typeof window !== 'undefined' ? window : globalThis).CDCD ||
           ((typeof window !== 'undefined' ? window : globalThis).CDCD = {});

(function (CDCD) {
  'use strict';

  var session = null;

  function el(id) { return document.getElementById(id); }

  function esc(s) {
    return String(s)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;');
  }

  function readConfig() {
    var mode = document.querySelector('input[name="mode"]:checked').value;
    var modes = {
      spot: mode === 'spot' || mode === 'both',
      picker: mode === 'picker' || mode === 'both'
    };
    var tiers = {
      1: el('tier-basic').checked,
      2: el('tier-medium').checked,
      3: el('tier-full').checked
    };
    return { modes: modes, tiers: tiers };
  }

  function makeSeed(raw) {
    var trimmed = String(raw || '').trim();
    if (trimmed === '') {
      return ((Date.now() & 0x7fffffff) >>> 0);
    }
    var n = parseInt(trimmed, 10);
    return isNaN(n) ? 0xC0FFEE : (n >>> 0);
  }

  function newSession() {
    var seed = makeSeed(el('seed-input').value);
    el('seed-input').value = seed;
    var rng = CDCD.mulberry32(seed);
    session = CDCD.createSession(rng, readConfig());
    renderNext();
  }

  function renderScore() {
    var s = CDCD.getScore(session);
    el('score').textContent = 'Score: ' + s.right + ' / ' + s.total;
  }

  function renderQuestion() {
    var cur = CDCD.getCurrent(session);
    if (!cur) {
      el('question').innerHTML =
        '<p class="empty">No questions match the current filters.</p>';
      el('options').innerHTML = '';
      el('feedback').innerHTML = '';
      return;
    }
    var q = cur.q;
    var html = '<div class="qhead">' +
      '<span class="tag mode-' + q.mode + '">' + q.mode + '</span>' +
      '<span class="tag tier-' + q.tier + '">tier ' + q.tier + '</span>' +
      '</div>';
    html += '<p class="stem">' + esc(q.stem) + '</p>';
    if (q.diagram) {
      html += '<pre class="diagram">' + esc(q.diagram) + '</pre>';
    }
    el('question').innerHTML = html;

    var optsHtml = '';
    var type = q.mode === 'spot' ? 'checkbox' : 'radio';
    var name = q.mode === 'spot' ? 'spot-opt' : 'picker-opt';
    for (var i = 0; i < cur.options.length; i++) {
      var o = cur.options[i];
      optsHtml += '<label class="option">' +
        '<input type="' + type + '" name="' + name + '" value="' + i + '"> ' +
        esc(o.text) + '</label>';
    }
    optsHtml += '<div class="submit-wrap">' +
      '<button type="button" id="submit-answer" class="primary">Submit</button>' +
      '</div>';
    el('options').innerHTML = optsHtml;

    var inputs = el('options').querySelectorAll('input');
    for (var j = 0; j < inputs.length; j++) {
      inputs[j].addEventListener('change', onSelectionChange);
    }
    el('submit-answer').addEventListener('click', onSubmit);
    el('feedback').innerHTML = '';
  }

  function onSelectionChange(ev) {
    var cur = CDCD.getCurrent(session);
    if (!cur || cur.answered) {
      return;
    }
    var idx = parseInt(ev.target.value, 10);
    if (cur.q.mode === 'spot') {
      CDCD.toggleSelection(session, idx);
    } else {
      CDCD.setSingleSelection(session, idx);
      var inputs = el('options').querySelectorAll('input');
      for (var i = 0; i < inputs.length; i++) {
        inputs[i].checked = parseInt(inputs[i].value, 10) === idx;
      }
    }
  }

  function onSubmit() {
    var result = CDCD.submitAnswer(session);
    if (!result) {
      return;
    }
    renderFeedback(result);
    renderScore();
  }

  function renderFeedback(result) {
    var cur = CDCD.getCurrent(session);
    var html = '<p class="verdict ' + (result.right ? 'good' : 'bad') + '">' +
      (result.right ? 'Correct.' : 'Not quite.') + '</p>';
    html += '<p class="explanation">' + esc(result.q.explanation) + '</p>';
    html += '<ul class="option-explanations">';
    for (var i = 0; i < cur.options.length; i++) {
      var o = cur.options[i];
      var cls = 'neutral';
      var marker = '';
      if (o.correct) {
        cls = 'correct-opt';
        marker = '[correct] ';
      } else if (result.selected.indexOf(i) !== -1) {
        cls = 'wrong-selected';
        marker = '[selected] ';
      }
      html += '<li class="' + cls + '">' + marker + '<strong>' +
        esc(o.text) + '</strong> &mdash; ' + esc(o.explanation) + '</li>';
    }
    html += '</ul>';
    html += '<div class="submit-wrap">' +
      '<button type="button" id="next-question" class="primary">Next ' +
      'question</button></div>';
    el('feedback').innerHTML = html;
    el('next-question').addEventListener('click', renderNext);
  }

  function renderNext() {
    CDCD.nextQuestion(session);
    renderQuestion();
    renderScore();
  }

  function init() {
    el('new-session').addEventListener('click', newSession);
    var radios = document.querySelectorAll('input[name="mode"]');
    for (var i = 0; i < radios.length; i++) {
      radios[i].addEventListener('change', newSession);
    }
    el('tier-basic').addEventListener('change', newSession);
    el('tier-medium').addEventListener('change', newSession);
    el('tier-full').addEventListener('change', newSession);
    newSession();
  }

  CDCD.app = { init: init, newSession: newSession };
})(CDCD);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = CDCD;
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', function () {
    CDCD.app.init();
  });
}
