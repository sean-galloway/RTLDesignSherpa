// model.js -- setup/hold slack and pipelining explorer for slack_explorer.
//
// Pure functions, no DOM. Dual-environment header: the same bytes run in the
// browser (window.SLACK) and under node (module.exports).
var SLACK = (typeof window !== 'undefined' ? window : globalThis).SLACK ||
            ((typeof window !== 'undefined' ? window : globalThis).SLACK = {});

(function (SLACK) {
  'use strict';

  var FIELDS = ['T', 'tCO', 'tLOGIC', 'tROUTE', 'skew', 'tSU', 'tHD', 'K'];

  function coerce(p) {
    var out = {};
    FIELDS.forEach(function (f) {
      out[f] = typeof p[f] === 'string' && p[f].trim() !== '' ? Number(p[f]) : p[f];
    });
    return out;
  }

  // Returns {ok, errors} where errors maps field -> message. Numeric strings
  // are accepted (input elements deliver strings). Skew may be negative.
  function validate(p) {
    var v = coerce(p);
    var errors = {};
    function isNum(x) { return typeof x === 'number' && isFinite(x); }
    function isPosInt(x, min) { return isNum(x) && x >= min && Math.floor(x) === x; }

    if (!isNum(v.T) || v.T <= 0) { errors.T = 'must be > 0'; }
    if (!isNum(v.tCO) || v.tCO < 0) { errors.tCO = 'must be >= 0'; }
    if (!isNum(v.tLOGIC) || v.tLOGIC < 0) { errors.tLOGIC = 'must be >= 0'; }
    if (!isNum(v.tROUTE) || v.tROUTE < 0) { errors.tROUTE = 'must be >= 0'; }
    if (!isNum(v.skew)) { errors.skew = 'must be a number'; }
    if (!isNum(v.tSU) || v.tSU < 0) { errors.tSU = 'must be >= 0'; }
    if (!isNum(v.tHD) || v.tHD < 0) { errors.tHD = 'must be >= 0'; }
    if (!isPosInt(v.K, 1) || v.K > 4) { errors.K = 'must be an integer 1..4'; }
    return { ok: Object.keys(errors).length === 0, errors: errors };
  }

  // Setup slack: time available minus time required, accounting for skew.
  // Positive launch skew (launch later / capture earlier) steals setup margin.
  function setupSlack(p) {
    return p.T - p.tCO - p.tLOGIC - p.tROUTE + p.skew - p.tSU;
  }

  // Hold slack: shortest data path minus hold requirement, accounting for skew.
  // Positive launch skew (launch later / capture earlier) improves hold margin.
  function holdSlack(p) {
    return p.tCO + p.tLOGIC + p.tROUTE - p.skew - p.tHD;
  }

  function hint(setupFail, holdFail) {
    if (setupFail && holdFail) {
      return 'Both violations: reduce logic delay or pipeline for setup; ' +
             'add min-delay / insert buffer for hold.';
    }
    if (setupFail) {
      return 'Setup violation: reduce logic delay, pipeline, increase period, ' +
             'or use positive skew.';
    }
    if (holdFail) {
      return 'Hold violation: add min-delay / insert buffer ' +
             '(hold is fixed with MORE delay). Skewing launch earlier helps.';
    }
    return 'PASS: both setup and hold margins are positive.';
  }

  // Only call with already-valid input. Returns the full slack analysis.
  function computeSlack(p) {
    var s = setupSlack(p);
    var h = holdSlack(p);
    var setupFail = s < 0;
    var holdFail = h < 0;
    return {
      setupSlack: s,
      holdSlack: h,
      setupPass: !setupFail,
      holdPass: !holdFail,
      pass: !setupFail && !holdFail,
      hint: hint(setupFail, holdFail)
    };
  }

  // Pipeline model: total combinational delay is split into K balanced stages.
  // Per-stage logic = (tLOGIC + tROUTE) / K. Skew is not included here.
  // minPeriod = tCO + stageLogic + tSU. Frequency returned in MHz when
  // delays are in nanoseconds.
  function computePipeline(p, K) {
    var stageLogic = (p.tLOGIC + p.tROUTE) / K;
    var minPeriod = p.tCO + stageLogic + p.tSU;
    var maxFreq = 1000 / minPeriod;
    return {
      K: K,
      stageLogic: stageLogic,
      minPeriod: minPeriod,
      maxFreq: maxFreq,
      latency: K,
      closesWithT: p.T >= minPeriod
    };
  }

  // Table for K = 1..4 using the current T.
  function computePipelineTable(p) {
    var table = [];
    for (var K = 1; K <= 4; K += 1) {
      table.push(computePipeline(p, K));
    }
    return table;
  }

  // Only call with already-valid input. Returns a unified result for both
  // panels plus the original parameters for reference.
  function compute(p) {
    return {
      params: p,
      slack: computeSlack(p),
      pipeline: {
        K: p.K,
        selected: computePipeline(p, p.K),
        table: computePipelineTable(p)
      }
    };
  }

  SLACK.validate = validate;
  SLACK.coerce = coerce;
  SLACK.setupSlack = setupSlack;
  SLACK.holdSlack = holdSlack;
  SLACK.computeSlack = computeSlack;
  SLACK.computePipeline = computePipeline;
  SLACK.computePipelineTable = computePipelineTable;
  SLACK.compute = compute;
})(SLACK);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = SLACK;
}
