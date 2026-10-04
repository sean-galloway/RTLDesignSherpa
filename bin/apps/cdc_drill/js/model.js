// model.js -- CDC drill session engine.
//
// Pure logic, no DOM. Builds a shuffled pool from the content generators,
// presents one question at a time, scores answers, and tracks the session.
// All randomness uses the rng passed to createSession. Dual-environment header
// so the same bytes run in the browser and under node.
var CDCD = (typeof window !== 'undefined' ? window : globalThis).CDCD ||
           ((typeof window !== 'undefined' ? window : globalThis).CDCD = {});

(function (CDCD) {
  'use strict';

  function arraysEqual(a, b) {
    if (a.length !== b.length) {
      return false;
    }
    for (var i = 0; i < a.length; i++) {
      if (a[i] !== b[i]) {
        return false;
      }
    }
    return true;
  }

  function correctIndices(options) {
    var out = [];
    for (var i = 0; i < options.length; i++) {
      if (options[i].correct) {
        out.push(i);
      }
    }
    return out;
  }

  // createSession(rng, config) -> session object
  // config:
  //   tiers  : {1: bool, 2: bool, 3: bool}  (default all true)
  //   modes  : {spot: bool, picker: bool}   (default all true)
  function createSession(rng, config) {
    config = config || {};
    var tiers = config.tiers || { 1: true, 2: true, 3: true };
    var modes = config.modes || { spot: true, picker: true };
    var pool = [];
    if (modes.spot) {
      pool = pool.concat(CDCD.generateSpotQuestions(rng, tiers));
    }
    if (modes.picker) {
      pool = pool.concat(CDCD.generatePickerQuestions(rng, tiers));
    }
    pool = CDCD.rshuffle(rng, pool);
    return {
      rng: rng,
      pool: pool,
      index: 0,
      score: { right: 0, total: 0 },
      current: null
    };
  }

  // nextQuestion(session) -> current question view or null if pool empty.
  // The options are shuffled; the session remembers the shuffled order.
  function nextQuestion(session) {
    if (session.pool.length === 0) {
      session.current = null;
      return null;
    }
    if (session.index >= session.pool.length) {
      session.pool = CDCD.rshuffle(session.rng, session.pool);
      session.index = 0;
    }
    var q = session.pool[session.index++];
    var shuffled = CDCD.rshuffle(session.rng, q.options.slice());
    session.current = {
      q: q,
      options: shuffled,
      answered: false,
      selected: []
    };
    return session.current;
  }

  // toggleSelection(session, shuffledIndex) -- for spot multi-select.
  // For picker mode, callers should clear other selections so only one is
  // selected; this layer is agnostic.
  function toggleSelection(session, idx) {
    if (!session.current || session.current.answered) {
      return;
    }
    var sel = session.current.selected;
    var pos = -1;
    for (var i = 0; i < sel.length; i++) {
      if (sel[i] === idx) {
        pos = i;
        break;
      }
    }
    if (pos === -1) {
      sel.push(idx);
    } else {
      sel.splice(pos, 1);
    }
    sel.sort(function (a, b) { return a - b; });
  }

  // setSingleSelection(session, shuffledIndex) -- convenience for picker mode.
  function setSingleSelection(session, idx) {
    if (!session.current || session.current.answered) {
      return;
    }
    session.current.selected = [idx];
  }

  // submitAnswer(session) -> {right, selected, correctSet, q} or null.
  function submitAnswer(session) {
    if (!session.current || session.current.answered) {
      return null;
    }
    var cur = session.current;
    cur.answered = true;
    var correctSet = correctIndices(cur.options);
    var selected = cur.selected.slice();
    var right = false;
    if (cur.q.mode === 'spot') {
      right = arraysEqual(selected, correctSet);
    } else {
      right = selected.length === 1 && selected[0] === correctSet[0];
    }
    session.score.total++;
    if (right) {
      session.score.right++;
    }
    return {
      right: right,
      selected: selected,
      correctSet: correctSet,
      q: cur.q
    };
  }

  function getScore(session) {
    return session.score;
  }

  function getCurrent(session) {
    return session.current;
  }

  CDCD.createSession = createSession;
  CDCD.nextQuestion = nextQuestion;
  CDCD.toggleSelection = toggleSelection;
  CDCD.setSingleSelection = setSingleSelection;
  CDCD.submitAnswer = submitAnswer;
  CDCD.getScore = getScore;
  CDCD.getCurrent = getCurrent;
})(CDCD);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = CDCD;
}
