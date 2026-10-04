// model.js -- async FIFO almost-full / almost-empty threshold engine.
//
// Pure functions, no DOM. Dual-environment header: the same bytes run in the
// browser (window.FIFOFLAGS) and under node (module.exports).
//
// Convention for an async FIFO with N-stage pointer synchronizers:
//   - The write side sees the synchronized read pointer delayed by at most
//     (N + 1) read clocks (sample + N sync stages + 1 more read clock of
//     pointer movement before the sample is stable).
//   - The read side sees the synchronized write pointer delayed by at most
//     (N + 1) write clocks.
// Converting the write-side uncertainty into write-side items gives
//   margin_AF = ceil(f_wr / f_rd) * (N + 1).
// Converting the read-side uncertainty into read-side items gives
//   margin_AE = ceil(f_rd / f_wr) * (N + 1).
// These are conservative, integer, worst-case margins.
//
// The user additionally supplies a bubble tolerance B% of the FIFO depth.
// bubble_items = round(depth * B / 100).  The bubble is taken from each end:
//   AF_threshold = depth - margin_AF - bubble_items
//   AE_threshold = margin_AE + bubble_items
// The thresholds are valid only if AF_threshold > AE_threshold.
var FIFOFLAGS = (typeof window !== 'undefined' ? window : globalThis).FIFOFLAGS || ((typeof window !== 'undefined' ? window : globalThis).FIFOFLAGS = {});

(function (FF) {
  'use strict';

  var EXAMPLES = [
    { case: 1, depth: 32, fWr: 100, fRd: 100, nSync: 2, bubblePct: 10,
      note: 'Symmetric clocks: equal margins at both ends' },
    { case: 2, depth: 64, fWr: 200, fRd: 100, nSync: 2, bubblePct: 10,
      note: 'Fast writer: larger almost-full margin' },
    { case: 3, depth: 64, fWr: 100, fRd: 200, nSync: 2, bubblePct: 10,
      note: 'Fast reader: larger almost-empty margin' }
  ];

  var FIELDS = ['depth', 'fWr', 'fRd', 'nSync', 'bubblePct'];

  function coerce(p) {
    var out = {};
    FIELDS.forEach(function (f) {
      out[f] = typeof p[f] === 'string' && p[f].trim() !== '' ? Number(p[f]) : p[f];
    });
    return out;
  }

  function validate(p) {
    var v = coerce(p);
    var errors = {};
    function isNum(x) { return typeof x === 'number' && isFinite(x); }

    if (!isNum(v.depth) || v.depth < 1 || Math.floor(v.depth) !== v.depth) {
      errors.depth = 'must be an integer >= 1';
    }
    if (!isNum(v.fWr) || v.fWr <= 0) { errors.fWr = 'must be > 0'; }
    if (!isNum(v.fRd) || v.fRd <= 0) { errors.fRd = 'must be > 0'; }
    if (!isNum(v.nSync) || v.nSync < 0 || Math.floor(v.nSync) !== v.nSync) {
      errors.nSync = 'must be an integer >= 0';
    }
    if (!isNum(v.bubblePct) || v.bubblePct < 0 || v.bubblePct > 100) {
      errors.bubblePct = 'must be between 0 and 100';
    }
    return { ok: Object.keys(errors).length === 0, errors: errors };
  }

  // Only call with already-valid input.
  function compute(p) {
    var marginAF = Math.ceil(p.fWr / p.fRd) * (p.nSync + 1);
    var marginAE = Math.ceil(p.fRd / p.fWr) * (p.nSync + 1);
    var bubbleItems = Math.round(p.depth * p.bubblePct / 100);
    var afThreshold = p.depth - marginAF - bubbleItems;
    var aeThreshold = marginAE + bubbleItems;
    var pass = afThreshold > aeThreshold;

    var message;
    if (pass) {
      message = 'PASS: AF threshold is above AE threshold';
    } else {
      message = 'FAIL: depth is too small for the chosen margins and bubble';
    }

    return {
      ok: true,
      depth: p.depth,
      fWr: p.fWr,
      fRd: p.fRd,
      nSync: p.nSync,
      bubblePct: p.bubblePct,
      marginAF: marginAF,
      marginAE: marginAE,
      bubbleItems: bubbleItems,
      afThreshold: afThreshold,
      aeThreshold: aeThreshold,
      pass: pass,
      message: message
    };
  }

  FF.validate = validate;
  FF.compute = compute;
  FF.EXAMPLES = EXAMPLES;
})(FIFOFLAGS);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = FIFOFLAGS;
}
