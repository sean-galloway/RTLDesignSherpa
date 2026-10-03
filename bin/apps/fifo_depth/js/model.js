// model.js -- async FIFO depth calculation engine for fifo_depth.
//
// A faithful port of docs/fifo_depth_calculator_v2.xlsx: worst-case burst
// sizing with synchronizer margin and encoding-aware depth output. The
// operation order below matches the spreadsheet exactly (see the spec,
// docs/superpowers/specs/2026-10-03-fifo-depth-app-design.md section 3) --
// the floor() on itemsRead is sensitive to IEEE-754 ordering.
//
// Pure functions, no DOM. Dual-environment header: the same bytes run in
// the browser (window.FD) and under node (module.exports).
var FD = (typeof window !== 'undefined' ? window : globalThis).FD ||
         ((typeof window !== 'undefined' ? window : globalThis).FD = {});

(function (FD) {
  'use strict';

  // The six example cases from the sheet's "Example Cases" tab, notes
  // verbatim. Rendered as the click-to-load table and used as golden
  // regression values by test/run_tests.js.
  var EXAMPLES = [
    { case: 1, fA: 80, fB: 50, burst: 120, wIdle: 0, rIdle: 0, nSync: 2,
      note: 'Baseline: 80 MHz writer into a 50 MHz reader' },
    { case: 2, fA: 100, fB: 90, burst: 120, wIdle: 0, rIdle: 0, nSync: 2,
      note: 'Close frequencies - small residual depth' },
    { case: 3, fA: 50, fB: 50, burst: 120, wIdle: 1, rIdle: 3, nSync: 2,
      note: 'Equal frequency, reader duty-limited by idle cycles' },
    { case: 4, fA: 30, fB: 50, burst: 120, wIdle: 1, rIdle: 3, nSync: 2,
      note: 'fA < fB in Hz, but idle cycles invert it: 15 vs 12.5 Mwords/s, so depth is still needed' },
    { case: 5, fA: 200, fB: 100, burst: 256, wIdle: 0, rIdle: 0, nSync: 3,
      note: 'Wide-bus stream style, 3-stage synchronizer' },
    { case: 6, fA: 80, fB: 50, burst: 120, wIdle: 0, rIdle: 0, nSync: 3,
      note: 'Baseline with a 3-stage synchronizer (one more slot)' }
  ];

  var FIELDS = ['fA', 'fB', 'burst', 'wIdle', 'rIdle', 'nSync'];

  function coerce(p) {
    var out = {};
    FIELDS.forEach(function (f) {
      out[f] = typeof p[f] === 'string' && p[f].trim() !== '' ? Number(p[f]) : p[f];
    });
    return out;
  }

  // Returns {ok, errors} where errors maps field -> message. Numeric
  // strings are accepted (input elements deliver strings).
  function validate(p) {
    var v = coerce(p);
    var errors = {};
    function isNum(x) { return typeof x === 'number' && isFinite(x); }

    if (!isNum(v.fA) || v.fA <= 0) { errors.fA = 'must be > 0'; }
    if (!isNum(v.fB) || v.fB <= 0) { errors.fB = 'must be > 0'; }
    if (!isNum(v.burst) || v.burst < 1 || Math.floor(v.burst) !== v.burst) {
      errors.burst = 'must be an integer >= 1';
    }
    if (!isNum(v.wIdle) || v.wIdle < 0 || Math.floor(v.wIdle) !== v.wIdle) {
      errors.wIdle = 'must be an integer >= 0';
    }
    if (!isNum(v.rIdle) || v.rIdle < 0 || Math.floor(v.rIdle) !== v.rIdle) {
      errors.rIdle = 'must be an integer >= 0';
    }
    if (!isNum(v.nSync) || v.nSync < 0 || Math.floor(v.nSync) !== v.nSync) {
      errors.nSync = 'must be an integer >= 0';
    }
    return { ok: Object.keys(errors).length === 0, errors: errors };
  }

  // Only call with already-valid input. Operation order matches the sheet.
  function compute(p) {
    var writeNsPerItem = (1 + p.wIdle) * 1000 / p.fA;
    var writeNsTotal = p.burst * writeNsPerItem;
    var readNsPerItem = (1 + p.rIdle) * 1000 / p.fB;
    var itemsRead = Math.floor(writeNsTotal / readNsPerItem);
    var rawDepth = Math.max(1, p.burst - itemsRead);
    var totalDepth = rawDepth + p.nSync;
    var grayDepth = Math.pow(2, Math.ceil(Math.log2(Math.max(totalDepth, 2))));
    var johnsonDepth = totalDepth % 2 === 0 ? totalDepth : totalDepth + 1;
    var savingsSlots = grayDepth - johnsonDepth;
    var savingsPct = grayDepth === 0 ? 0 : Math.round((savingsSlots / grayDepth) * 1000) / 1000;

    return {
      ok: true,
      writeNsPerItem: writeNsPerItem,
      writeNsTotal: writeNsTotal,
      readNsPerItem: readNsPerItem,
      itemsRead: itemsRead,
      rawDepth: rawDepth,
      totalDepth: totalDepth,
      grayDepth: grayDepth,
      johnsonDepth: johnsonDepth,
      savingsSlots: savingsSlots,
      savingsPct: savingsPct,
      steady: {
        writeRate: p.fA / (1 + p.wIdle),
        readRate: p.fB / (1 + p.rIdle),
        drainable: p.fA / (1 + p.wIdle) <= p.fB / (1 + p.rIdle)
      }
    };
  }

  FD.validate = validate;
  FD.compute = compute;
  FD.EXAMPLES = EXAMPLES;
})(FD);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = FD;
}
