// timing.js -- Mode 2: timing-parameter drill.
//
// Pure layer (node-tested, registered on DDRD):
//   computeScope(topo, a, b)         -> scope string for a command pair
//   patternMatch(pattern, cmdType)   -> bool ('|' alternation, '*' wildcard)
//   matchParams(pack, topo, a, b)    -> [symbols] constraining the a->b gap
//   timingCandidatePairs(cmds)       -> [{prevIdx, nextIdx}] askable gaps
//   buildTimingQuestion(pack, rng)   -> a full question object
//
// UI layer (browser only): DDRD.timingMode = { mount, unmount }. Shows a
// command sequence with one gap highlighted; the learner checks every
// timing parameter that constrains that gap. Exact-set scoring with
// "missing:/extra:" feedback plus each correct parameter's definition. A
// reference panel (all pack timingParams grouped by chapter) toggles open
// mid-question without affecting scoring.
//
// Scope model (documented in notes/design.md):
//   same_bank   same bank number AND same SID
//   same_group  different banks, one bank group (BG topologies only)
//   diff_group  banks in different bank groups (BG topologies only)
//   diff_bank   different banks (flat topologies only)
//   diff_sid    different Stack IDs (sid-aware topologies only)
// A rule matches when rule.scope === 'any', or rule.scope === the computed
// scope, or rule.scope === 'diff_bank' and the computed scope is diff_group
// or diff_sid (different groups/stacks are by construction different banks
// -- the one-way subsumption that lets a flat-tech rule port to a BG tech).
// same_bank does NOT subsume into same_group: packs list both scopes
// explicitly (see notes/timing-tables.md).
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  // -- pure layer ------------------------------------------------------------

  function computeScope(topo, a, b) {
    if (topo.sids > 0 && a.sid !== undefined && a.sid !== null &&
        b.sid !== undefined && b.sid !== null && a.sid !== b.sid) {
      return 'diff_sid';
    }
    if (a.bank === b.bank) {
      return 'same_bank';
    }
    if (topo.hasBankGroups) {
      return DDRD.bg(topo, a.bank) === DDRD.bg(topo, b.bank)
        ? 'same_group'
        : 'diff_group';
    }
    return 'diff_bank';
  }

  function patternMatch(pattern, cmdType) {
    var alts = pattern.split('|');
    for (var i = 0; i < alts.length; i++) {
      if (alts[i] === '*' || alts[i] === cmdType) {
        return true;
      }
    }
    return false;
  }

  function scopeMatches(ruleScope, computed) {
    if (ruleScope === 'any' || ruleScope === computed) {
      return true;
    }
    return ruleScope === 'diff_bank' &&
           (computed === 'diff_group' || computed === 'diff_sid');
  }

  // Every timing parameter with at least one appliesTo rule matching the
  // a->b transition, in pack order.
  function matchParams(pack, topo, a, b) {
    if (a.annotation || b.annotation) {
      return [];
    }
    var computed = computeScope(topo, a, b);
    var out = [];
    pack.timingParams.forEach(function (p) {
      var hit = p.appliesTo.some(function (rule) {
        return patternMatch(rule.from, a.type) &&
               patternMatch(rule.to, b.type) &&
               scopeMatches(rule.scope, computed);
      });
      if (hit) {
        out.push(p.symbol);
      }
    });
    return out;
  }

  // Askable gaps: pairs of consecutive REAL commands (annotations skipped,
  // so a gap may span a turnaround annotation) with at least one matching
  // parameter. Indices point into the original cmds array.
  function timingCandidatePairs(pack, topo, cmds) {
    var realIdx = [];
    for (var i = 0; i < cmds.length; i++) {
      if (!cmds[i].annotation) {
        realIdx.push(i);
      }
    }
    var out = [];
    for (var k = 0; k + 1 < realIdx.length; k++) {
      var a = cmds[realIdx[k]];
      var b = cmds[realIdx[k + 1]];
      if (matchParams(pack, topo, a, b).length > 0) {
        out.push({ prevIdx: realIdx[k], nextIdx: realIdx[k + 1] });
      }
    }
    return out;
  }

  // buildTimingQuestion(pack, rng) -> {
  //   genId, window: [Cmd] (real cmds only, annotations dropped),
  //   gapAfter: index into window of the gap's first command,
  //   answer: [symbols], allSymbols: [symbols] (every pack param)
  // }
  // The window keeps up to WINDOW_BEFORE real commands before the gap and
  // WINDOW_AFTER after it, so long schedules stay readable.
  var WINDOW_BEFORE = 3;
  var WINDOW_AFTER = 2;

  function buildTimingQuestion(pack, rng) {
    var topo = pack.topology;
    var avail = DDRD.availableGenerators(topo);
    for (var attempt = 0; attempt < 40; attempt++) {
      var gen = DDRD.rpick(rng, avail);
      var policy = (pack.scenarioTweaks &&
                    pack.scenarioTweaks.defaultPolicy) || 'open';
      var sc = DDRD.buildScenario(gen, topo, policy, rng);
      var pairs = timingCandidatePairs(pack, topo, sc.correct.cmds);
      if (pairs.length === 0) {
        continue;
      }
      var pair = DDRD.rpick(rng, pairs);
      var answer = matchParams(pack, topo,
                               sc.correct.cmds[pair.prevIdx],
                               sc.correct.cmds[pair.nextIdx]);
      var real = DDRD.real_cmds(sc.correct.cmds);
      // Indices of the pair within the annotation-free real list.
      var realPrev = 0;
      var seen = -1;
      for (var i = 0; i < sc.correct.cmds.length; i++) {
        if (!sc.correct.cmds[i].annotation) {
          seen++;
        }
        if (i === pair.prevIdx) {
          realPrev = seen;
          break;
        }
      }
      var start = Math.max(0, realPrev - WINDOW_BEFORE);
      var end = Math.min(real.length, realPrev + 1 + 1 + WINDOW_AFTER);
      return {
        genId: sc.id,
        window: real.slice(start, end),
        gapAfter: realPrev - start,
        answer: answer,
        allSymbols: pack.timingParams.map(function (p) { return p.symbol; })
      };
    }
    throw new Error('buildTimingQuestion: no askable gap in 40 attempts');
  }

  DDRD.computeScope = computeScope;
  DDRD.patternMatch = patternMatch;
  DDRD.matchParams = matchParams;
  DDRD.timingCandidatePairs = timingCandidatePairs;
  DDRD.buildTimingQuestion = buildTimingQuestion;

  // -- UI layer (browser only) ------------------------------------------------

  if (typeof window === 'undefined' || !window.document) {
    return;
  }

  var st = null; // per-mount state

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) { e.className = cls; }
    if (text !== undefined) { e.textContent = text; }
    return e;
  }

  function paramBySymbol(pack, symbol) {
    for (var i = 0; i < pack.timingParams.length; i++) {
      if (pack.timingParams[i].symbol === symbol) {
        return pack.timingParams[i];
      }
    }
    return null;
  }

  function renderQuestion() {
    var q = st.question;
    st.seqEl.innerHTML = '';
    q.window.forEach(function (cmd, i) {
      st.seqEl.appendChild(el('div', 'timing-cmd', DDRD.format_cmd(cmd)));
      if (i === q.gapAfter) {
        st.seqEl.appendChild(el('div', 'timing-gap',
          '? -- which timing parameters constrain this gap?'));
      }
    });

    st.optionsEl.innerHTML = '';
    st.checked = {};
    // Options grouped by chapter, in pack order.
    var chapters = [];
    var byChapter = {};
    st.pack.timingParams.forEach(function (p) {
      if (!byChapter[p.chapter]) {
        byChapter[p.chapter] = [];
        chapters.push(p.chapter);
      }
      byChapter[p.chapter].push(p);
    });
    chapters.forEach(function (ch) {
      st.optionsEl.appendChild(el('div', 'timing-opt-chapter', ch));
      byChapter[ch].forEach(function (p) {
        var lab = el('label', 'timing-opt');
        var cb = document.createElement('input');
        cb.type = 'checkbox';
        cb.disabled = false;
        cb.addEventListener('change', function () {
          st.checked[p.symbol] = cb.checked;
        });
        lab.appendChild(cb);
        lab.appendChild(document.createTextNode(' ' + p.symbol));
        st.optionsEl.appendChild(lab);
      });
    });

    st.feedbackEl.innerHTML = '';
    st.submitBtn.disabled = false;
  }

  function newQuestion() {
    st.question = DDRD.buildTimingQuestion(st.pack, st.rng);
    renderQuestion();
  }

  function submit() {
    var q = st.question;
    var picked = q.allSymbols.filter(function (s) { return st.checked[s]; });
    var answerSet = {};
    q.answer.forEach(function (s) { answerSet[s] = true; });
    var pickedSet = {};
    picked.forEach(function (s) { pickedSet[s] = true; });

    var missing = q.answer.filter(function (s) { return !pickedSet[s]; });
    var extra = picked.filter(function (s) { return !answerSet[s]; });
    var right = missing.length === 0 && extra.length === 0;

    st.score.total++;
    if (right) { st.score.right++; }

    st.submitBtn.disabled = true;
    st.optionsEl.querySelectorAll('input').forEach(function (cb) {
      cb.disabled = true;
    });

    st.feedbackEl.innerHTML = '';
    st.feedbackEl.appendChild(el('p',
      'timing-verdict ' + (right ? 'good' : 'bad'),
      right ? 'Correct - exactly the governing parameters.'
            : 'Not quite.'));
    if (!right) {
      var detail = [];
      if (missing.length > 0) { detail.push('missing: ' + missing.join(', ')); }
      if (extra.length > 0) { detail.push('extra: ' + extra.join(', ')); }
      st.feedbackEl.appendChild(el('p', 'timing-setdiff',
        detail.join('; ')));
    }
    q.answer.forEach(function (s) {
      var p = paramBySymbol(st.pack, s);
      st.feedbackEl.appendChild(el('p', 'timing-def',
        s + ' -- ' + p.definition));
    });
    var next = el('button', 'timing-next', 'Next question');
    next.type = 'button';
    next.addEventListener('click', newQuestion);
    st.feedbackEl.appendChild(next);
    next.focus();
    renderScore();
  }

  function renderScore() {
    st.scoreEl.textContent = 'Score: ' + st.score.right + ' / ' +
                             st.score.total;
  }

  function toggleReference() {
    st.refOpen = !st.refOpen;
    st.refEl.hidden = !st.refOpen;
    st.refBtn.textContent = st.refOpen ? 'Hide timing reference'
                                       : 'Timing reference';
  }

  function buildReference() {
    var chapters = [];
    var byChapter = {};
    st.pack.timingParams.forEach(function (p) {
      if (!byChapter[p.chapter]) {
        byChapter[p.chapter] = [];
        chapters.push(p.chapter);
      }
      byChapter[p.chapter].push(p);
    });
    chapters.forEach(function (ch) {
      st.refEl.appendChild(el('h3', 'timing-ref-chapter', ch));
      var table = el('table', 'timing-ref-table');
      var head = el('tr', 'timing-ref-head');
      ['Symbol', 'Definition', 'Applies between'].forEach(function (h) {
        head.appendChild(el('th', null, h));
      });
      table.appendChild(head);
      byChapter[ch].forEach(function (p) {
        var row = el('tr');
        row.appendChild(el('td', 'timing-ref-symbol', p.symbol));
        row.appendChild(el('td', null, p.definition));
        row.appendChild(el('td', 'timing-ref-applies', p.appliesTo.map(
          function (r) {
            return r.from + ' -> ' + r.to + ' (' + r.scope + ')';
          }).join('; ')));
        table.appendChild(row);
      });
      st.refEl.appendChild(table);
    });
  }

  function mount(elRoot, pack) {
    st = {
      pack: pack,
      rng: DDRD.mulberry32((Date.now() & 0x7fffffff) >>> 0),
      question: null,
      checked: {},
      score: { right: 0, total: 0 },
      refOpen: false
    };

    var bar = el('div', 'timing-bar');
    st.refBtn = el('button', 'timing-ref-btn', 'Timing reference');
    st.refBtn.type = 'button';
    st.refBtn.addEventListener('click', toggleReference);
    bar.appendChild(st.refBtn);
    st.scoreEl = el('div', 'timing-score');
    bar.appendChild(st.scoreEl);
    elRoot.appendChild(bar);

    st.refEl = el('div', 'timing-reference');
    st.refEl.hidden = true;
    buildReference();
    elRoot.appendChild(st.refEl);

    st.seqEl = el('div', 'timing-sequence');
    elRoot.appendChild(st.seqEl);
    st.optionsEl = el('div', 'timing-options');
    elRoot.appendChild(st.optionsEl);

    st.submitBtn = el('button', 'timing-submit', 'Check answer');
    st.submitBtn.type = 'button';
    st.submitBtn.addEventListener('click', submit);
    elRoot.appendChild(st.submitBtn);

    st.feedbackEl = el('div', 'timing-feedback');
    elRoot.appendChild(st.feedbackEl);

    newQuestion();
    renderScore();
  }

  function unmount() { st = null; }

  DDRD.timingMode = { mount: mount, unmount: unmount };
})(DDRD);
