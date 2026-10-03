// quiz.js -- Mode 1: endless knowledge quiz, one question at a time.
// Correct answers are tracked by IDENTITY (answers[0] before shuffling),
// never by position. Registers as DDRD.quizMode = { mount, unmount }.
// Browser-only (DOM); logic worth testing lives in engine/scenarios.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  var st = null; // per-mount state

  function shuffle(arr, rng) {
    var a = arr.slice();
    for (var i = a.length - 1; i > 0; i--) {
      var j = Math.floor(rng() * (i + 1));
      var t = a[i]; a[i] = a[j]; a[j] = t;
    }
    return a;
  }

  function chapters(pack) {
    var seen = {};
    var out = [];
    pack.questionBank.forEach(function (q) {
      if (!seen[q.chapter]) { seen[q.chapter] = true; out.push(q.chapter); }
    });
    return out;
  }

  function buildPool() {
    var hardOnly = st.hardOnly;
    var active = st.activeChapters;
    st.pool = shuffle(st.pack.questionBank.filter(function (q) {
      return active[q.chapter] && (!hardOnly || q.hard);
    }), st.rng);
    st.poolIdx = 0;
  }

  function nextQuestion() {
    if (st.poolIdx >= st.pool.length) {
      st.pool = shuffle(st.pool, st.rng); // endless: reshuffle and continue
      st.poolIdx = 0;
    }
    if (st.pool.length === 0) {
      st.qEl.innerHTML = '<p class="quiz-empty">No questions match the ' +
        'current filters. Re-enable a chapter above.</p>';
      st.answersEl.innerHTML = '';
      st.feedbackEl.innerHTML = '';
      return;
    }
    var q = st.pool[st.poolIdx++];
    var correct = q.answers[0];
    var options = shuffle(q.answers, st.rng);
    st.current = { q: q, correct: correct, answered: false };

    st.qEl.innerHTML = '';
    var head = document.createElement('div');
    head.className = 'quiz-qhead';
    var tag = document.createElement('span');
    tag.className = 'quiz-chapter-tag';
    tag.textContent = q.chapter + (q.hard ? ' - hard' : '');
    head.appendChild(tag);
    var p = document.createElement('p');
    p.className = 'quiz-question';
    p.textContent = q.q;
    st.qEl.appendChild(head);
    st.qEl.appendChild(p);

    st.answersEl.innerHTML = '';
    options.forEach(function (text) {
      var b = document.createElement('button');
      b.type = 'button';
      b.className = 'quiz-answer';
      b.textContent = text;
      b.addEventListener('click', function () { answer(b, text); });
      st.answersEl.appendChild(b);
    });
    st.feedbackEl.innerHTML = '';
  }

  function answer(btn, text) {
    if (!st.current || st.current.answered) { return; }
    st.current.answered = true;
    var right = (text === st.current.correct);
    st.score.total++;
    if (right) { st.score.right++; }

    var buttons = st.answersEl.querySelectorAll('.quiz-answer');
    buttons.forEach(function (b) {
      b.disabled = true;
      if (b.textContent === st.current.correct) {
        b.classList.add('correct');
      }
    });
    if (!right) { btn.classList.add('wrong'); }

    var q = st.current.q;
    st.feedbackEl.innerHTML = '';
    var verdict = document.createElement('p');
    verdict.className = 'quiz-verdict ' + (right ? 'good' : 'bad');
    verdict.textContent = right ? 'Correct.' : 'Not quite.';
    var expl = document.createElement('p');
    expl.className = 'quiz-explanation';
    expl.textContent = q.explanation;
    var src = document.createElement('p');
    src.className = 'quiz-source';
    src.textContent = 'Source: ' + q.source;
    var next = document.createElement('button');
    next.type = 'button';
    next.className = 'quiz-next';
    next.textContent = 'Next question';
    next.addEventListener('click', function () { render(); });
    st.feedbackEl.appendChild(verdict);
    st.feedbackEl.appendChild(expl);
    st.feedbackEl.appendChild(src);
    st.feedbackEl.appendChild(next);
    next.focus();
    renderScore();
  }

  function renderScore() {
    st.scoreEl.textContent = 'Score: ' + st.score.right + ' / ' +
                             st.score.total;
  }

  function render() { nextQuestion(); renderScore(); }

  function mount(el, pack) {
    st = {
      pack: pack,
      rng: DDRD.mulberry32((Date.now() & 0x7fffffff) >>> 0),
      activeChapters: {},
      hardOnly: false,
      pool: [], poolIdx: 0,
      score: { right: 0, total: 0 },
      current: null
    };
    chapters(pack).forEach(function (c) { st.activeChapters[c] = true; });

    var filterBar = document.createElement('div');
    filterBar.className = 'quiz-filters';
    var label = document.createElement('span');
    label.className = 'quiz-filter-label';
    label.textContent = 'Chapters:';
    filterBar.appendChild(label);
    chapters(pack).forEach(function (c) {
      var lab = document.createElement('label');
      lab.className = 'quiz-filter';
      var cb = document.createElement('input');
      cb.type = 'checkbox';
      cb.checked = true;
      cb.addEventListener('change', function () {
        st.activeChapters[c] = cb.checked;
        buildPool();
        render();
      });
      lab.appendChild(cb);
      lab.appendChild(document.createTextNode(' ' + c));
      filterBar.appendChild(lab);
    });
    var hardLab = document.createElement('label');
    hardLab.className = 'quiz-filter quiz-filter-hard';
    var hardCb = document.createElement('input');
    hardCb.type = 'checkbox';
    hardCb.addEventListener('change', function () {
      st.hardOnly = hardCb.checked;
      buildPool();
      render();
    });
    hardLab.appendChild(hardCb);
    hardLab.appendChild(document.createTextNode(' hard only'));
    filterBar.appendChild(hardLab);

    st.scoreEl = document.createElement('div');
    st.scoreEl.className = 'quiz-score';
    filterBar.appendChild(st.scoreEl);

    st.qEl = document.createElement('div');
    st.qEl.className = 'quiz-body';
    st.answersEl = document.createElement('div');
    st.answersEl.className = 'quiz-answers';
    st.feedbackEl = document.createElement('div');
    st.feedbackEl.className = 'quiz-feedback';

    el.appendChild(filterBar);
    el.appendChild(st.qEl);
    el.appendChild(st.answersEl);
    el.appendChild(st.feedbackEl);

    buildPool();
    render();
  }

  function unmount() { st = null; }

  DDRD.quizMode = { mount: mount, unmount: unmount };
})(DDRD);
