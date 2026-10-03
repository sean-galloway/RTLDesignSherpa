// scenariodrill.js -- Mode 3: bank-state scheduling drill.
// Browser-only UI over scenarios.js + mutate.js: shows the initial bank
// states and the request list, offers the 4 schedule options buildScenario
// produced (index 0 correct; shuffled HERE, never in the model layer), and
// on answer shows the verdict, the generator's explanation, and the correct
// schedule with its per-command reasons. The pack's
// scenarioTweaks.excludeGenerators list is honored here (this UI is its
// consumer).
// Registers as DDRD.scenarioMode = { mount, unmount }.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  if (typeof window === 'undefined' || !window.document) {
    return;
  }

  var POLICY_LABEL = {
    open: 'open-page',
    close: 'close-page (auto-precharge)',
    frfcfs: 'FR-FCFS (one-level reorder)'
  };

  var st = null; // per-mount state

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) { e.className = cls; }
    if (text !== undefined) { e.textContent = text; }
    return e;
  }

  function shuffle(arr) {
    var a = arr.slice();
    for (var i = a.length - 1; i > 0; i--) {
      var j = Math.floor(st.rng() * (i + 1));
      var t = a[i]; a[i] = a[j]; a[j] = t;
    }
    return a;
  }

  function available() {
    var tweaks = st.pack.scenarioTweaks || {};
    var excluded = {};
    (tweaks.excludeGenerators || []).forEach(function (id) {
      excluded[id] = true;
    });
    return DDRD.availableGenerators(st.pack.topology).filter(function (g) {
      return st.tiers[g.tier] && !excluded[g.id];
    });
  }

  function renderBankState(sc) {
    var topo = st.pack.topology;
    var wrap = el('div', 'scen-banks');
    for (var b = 0; b < topo.banks; b++) {
      var entry = sc.bankState[b];
      var label = 'B' + b;
      if (topo.hasBankGroups) {
        label = 'G' + DDRD.bg(topo, b) + ' ' + label;
      }
      wrap.appendChild(el('span',
        'scen-bank' + (entry.openRow === null ? '' : ' scen-bank-open'),
        label + ': ' +
        (entry.openRow === null ? 'idle' : 'open R' + entry.openRow)));
    }
    return wrap;
  }

  function renderScheduleLines(container, cmds, reasons) {
    cmds.forEach(function (cmd, i) {
      var line = el('div', cmd.annotation ? 'scen-cmd scen-ann' : 'scen-cmd');
      line.textContent = DDRD.format_cmd(cmd);
      if (reasons && reasons[i]) {
        line.appendChild(el('span', 'scen-reason', '  ' + reasons[i]));
      }
      container.appendChild(line);
    });
  }

  function newScenario() {
    var gens = available();
    if (gens.length === 0) {
      st.promptEl.innerHTML = '';
      st.promptEl.appendChild(el('p', 'scen-empty',
        'No generators enabled. Re-enable a tier above.'));
      st.optionsEl.innerHTML = '';
      st.feedbackEl.innerHTML = '';
      return;
    }
    var gen = DDRD.rpick(st.rng, gens);
    var policy = (st.pack.scenarioTweaks &&
                  st.pack.scenarioTweaks.defaultPolicy) || 'open';
    var sc = DDRD.buildScenario(gen, st.pack.topology, policy, st.rng);
    st.scenario = sc;
    st.options = shuffle(sc.options);
    st.answered = false;

    st.promptEl.innerHTML = '';
    st.promptEl.appendChild(el('div', 'scen-tag',
      'tier ' + sc.tier + ' - ' + sc.id.replace(/_/g, ' ') +
      ' - policy: ' + (POLICY_LABEL[sc.policy] || sc.policy)));
    st.promptEl.appendChild(el('div', 'scen-subhead', 'Bank state'));
    st.promptEl.appendChild(renderBankState(sc));
    st.promptEl.appendChild(el('div', 'scen-subhead',
      'Requests (arrival order)'));
    var reqList = el('div', 'scen-reqs');
    sc.reqs.forEach(function (req, i) {
      reqList.appendChild(el('div', 'scen-req',
        (i + 1) + '. ' + DDRD.format_req(req)));
    });
    st.promptEl.appendChild(reqList);
    st.promptEl.appendChild(el('div', 'scen-subhead',
      'Which schedule is correct?'));

    st.optionsEl.innerHTML = '';
    st.options.forEach(function (opt) {
      var b = el('button', 'scen-option');
      b.type = 'button';
      var pre = el('div', 'scen-sched');
      renderScheduleLines(pre, opt.cmds, null);
      b.appendChild(pre);
      b.addEventListener('click', function () { answer(b, opt); });
      st.optionsEl.appendChild(b);
    });
    st.feedbackEl.innerHTML = '';
  }

  function answer(btn, opt) {
    if (st.answered) { return; }
    st.answered = true;
    var right = opt.correct === true;
    st.score.total++;
    if (right) { st.score.right++; }

    var buttons = st.optionsEl.querySelectorAll('.scen-option');
    buttons.forEach(function (b, i) {
      b.disabled = true;
      if (st.options[i].correct) {
        b.classList.add('correct');
      }
    });
    if (!right) { btn.classList.add('wrong'); }

    var sc = st.scenario;
    st.feedbackEl.innerHTML = '';
    st.feedbackEl.appendChild(el('p',
      'scen-verdict ' + (right ? 'good' : 'bad'),
      right ? 'Correct.' : 'Not quite - the highlighted schedule is right.'));
    if (sc.explanation) {
      st.feedbackEl.appendChild(el('p', 'scen-explanation', sc.explanation));
    }
    if (sc.reordered) {
      st.feedbackEl.appendChild(el('p', 'scen-reorder',
        'FR-FCFS served order: ' +
        sc.reordered.map(DDRD.format_req).join(' ; ')));
    }
    st.feedbackEl.appendChild(el('div', 'scen-subhead',
      'Why (per command)'));
    var why = el('div', 'scen-sched scen-why');
    renderScheduleLines(why, sc.correct.cmds, sc.correct.reasons);
    st.feedbackEl.appendChild(why);
    var next = el('button', 'scen-next', 'Next scenario');
    next.type = 'button';
    next.addEventListener('click', newScenario);
    st.feedbackEl.appendChild(next);
    next.focus();
    renderScore();
  }

  function renderScore() {
    st.scoreEl.textContent = 'Score: ' + st.score.right + ' / ' +
                             st.score.total;
  }

  function mount(elRoot, pack) {
    st = {
      pack: pack,
      rng: DDRD.mulberry32((Date.now() & 0x7fffffff) >>> 0),
      tiers: { 1: true, 2: true, 3: true },
      scenario: null,
      options: [],
      answered: false,
      score: { right: 0, total: 0 }
    };

    var bar = el('div', 'scen-bar');
    bar.appendChild(el('span', 'scen-filter-label', 'Tiers:'));
    [1, 2, 3].forEach(function (tier) {
      var lab = el('label', 'scen-filter');
      var cb = document.createElement('input');
      cb.type = 'checkbox';
      cb.checked = true;
      cb.addEventListener('change', function () {
        st.tiers[tier] = cb.checked;
        newScenario();
      });
      lab.appendChild(cb);
      lab.appendChild(document.createTextNode(' ' + tier));
      bar.appendChild(lab);
    });
    st.scoreEl = el('div', 'scen-score');
    bar.appendChild(st.scoreEl);
    elRoot.appendChild(bar);

    st.promptEl = el('div', 'scen-prompt');
    elRoot.appendChild(st.promptEl);
    st.optionsEl = el('div', 'scen-options');
    elRoot.appendChild(st.optionsEl);
    st.feedbackEl = el('div', 'scen-feedback');
    elRoot.appendChild(st.feedbackEl);

    newScenario();
    renderScore();
  }

  function unmount() { st = null; }

  DDRD.scenarioMode = { mount: mount, unmount: unmount };
})(DDRD);
