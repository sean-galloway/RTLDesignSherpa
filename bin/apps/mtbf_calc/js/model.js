// model.js -- Metastability MTBF calculator engine.
//
// Pedagogical implementation of the classic synchronizer MTBF formula:
//
//     MTBF = exp(C2 * tMET_total) / (C1 * f_clk * f_data)
//
// where N synchronizer stages contribute (N-1) full resolution periods r
// plus the input aperture term t0:
//
//     tMET_total = t0 + (N - 1) * r
//
// r is the per-stage resolving time available after accounting for clock
// to output (tCO) and setup (tSU):
//
//     r = (1 / f_clk) - tCO - tSU
//
// This convention follows the teaching in Clifford E. Cummings' SNUG
// synchronizer papers (e.g. "Synthesis and Scripting Techniques for
// Designing Multi-Asynchronous Clock Designs", SNUG 2001) where the
// metastability resolution budget grows by roughly one clock period for
// every additional synchronizer flop.
//
// The C1 / C2 technology constants are process-specific. The presets below
// are illustrative literature ballparks, not foundry numbers. C1 is in
// seconds; C2 is in s^-1 so that C2 * tMET_total is dimensionless.
//
// Pure functions, no DOM. Dual-environment header: the same bytes run in
// the browser (window.MTBF) and under node (module.exports).
var MTBF = (typeof window !== 'undefined' ? window : globalThis).MTBF ||
           ((typeof window !== 'undefined' ? window : globalThis).MTBF = {});

(function (MTBF) {
  'use strict';

  // Mission-time helpers.
  var SECONDS_PER_YEAR = 365.25 * 24 * 60 * 60;
  var SECONDS_PER_DAY = 24 * 60 * 60;
  var SECONDS_PER_HOUR = 60 * 60;
  var SECONDS_PER_MINUTE = 60;

  // Illustrative technology presets.  These are teaching values chosen to
  // produce the classic "microseconds -> minutes -> centuries" MTBF curve
  // at 1 GHz; real foundry constants differ and are usually quoted per
  // picosecond.  Each preset is labeled as illustrative in the UI.
  var PRESETS = [
    { name: '180 nm (illustrative)', c1: 2e-11, c2: 1.5e10,
      note: 'Older node: larger C1, smaller C2' },
    { name: '28 nm (illustrative)', c1: 1e-11, c2: 1.75e10,
      note: 'Mid-node baseline' },
    { name: '7 nm (illustrative)', c1: 5e-12, c2: 2.0e10,
      note: 'Advanced node: smaller C1, larger C2' }
  ];

  // Default input bundle.  The headline lesson is "2 flops at 1 GHz is not
  // enough for a year-long mission"; these defaults load that case.
  var DEFAULTS = {
    preset: '28 nm (illustrative)',
    c1: 1e-11,
    c2: 1.75e10,
    fData: 1e6,
    fClk: 1e9,
    tCO: 50e-12,
    tSU: 50e-12,
    t0: 10e-12,
    n: 2,
    missionYears: 1
  };

  // Numeric fields that may arrive as strings from <input> elements.
  var FIELDS = ['c1', 'c2', 'fData', 'fClk', 'tCO', 'tSU', 't0', 'n', 'missionYears'];

  function coerce(p) {
    var out = {};
    FIELDS.forEach(function (f) {
      out[f] = typeof p[f] === 'string' && p[f].trim() !== '' ? Number(p[f]) : p[f];
    });
    out.preset = p.preset || '';
    return out;
  }

  function isPosNum(x) {
    return typeof x === 'number' && isFinite(x) && x > 0;
  }

  function isNonNegNum(x) {
    return typeof x === 'number' && isFinite(x) && x >= 0;
  }

  // Returns {ok, errors}.  Numeric strings are accepted because input
  // elements deliver strings.
  function validate(p) {
    var v = coerce(p);
    var errors = {};

    if (!isPosNum(v.c1)) { errors.c1 = 'must be a positive number'; }
    if (!isPosNum(v.c2)) { errors.c2 = 'must be a positive number'; }
    if (!isPosNum(v.fData)) { errors.fData = 'must be > 0'; }
    if (!isPosNum(v.fClk)) { errors.fClk = 'must be > 0'; }
    if (!isNonNegNum(v.tCO)) { errors.tCO = 'must be >= 0'; }
    if (!isNonNegNum(v.tSU)) { errors.tSU = 'must be >= 0'; }
    if (!isPosNum(v.t0)) { errors.t0 = 'must be > 0'; }
    if (!isPosNum(v.n) || Math.floor(v.n) !== v.n || v.n < 1 || v.n > 4) {
      errors.n = 'must be an integer 1..4';
    }
    if (!isPosNum(v.missionYears)) { errors.missionYears = 'must be > 0'; }

    // Guard against a negative or zero resolution time.
    if (isPosNum(v.fClk) && isNonNegNum(v.tCO) && isNonNegNum(v.tSU)) {
      var period = 1 / v.fClk;
      var r = period - v.tCO - v.tSU;
      if (r <= 0) {
        errors.fClk = 'period must exceed tCO + tSU';
        errors.tCO = 'tCO + tSU must be less than clock period';
        errors.tSU = 'tCO + tSU must be less than clock period';
      }
    }

    return { ok: Object.keys(errors).length === 0, errors: errors };
  }

  // Compute tMET_total for a given N.
  function tMETFor(n, t0, r) {
    return t0 + (n - 1) * r;
  }

  // Classic synchronizer MTBF formula.  All times in seconds; frequencies
  // in Hz.  Returns MTBF in seconds.
  function mtbfSeconds(c1, c2, tMET, fClk, fData) {
    return Math.exp(c2 * tMET) / (c1 * fClk * fData);
  }

  // Convert a time in seconds to a human-friendly {value, unit} pair.
  function scaleSeconds(s) {
    if (typeof s !== 'number' || !isFinite(s) || s < 0) {
      return { value: NaN, unit: 's' };
    }
    if (s >= SECONDS_PER_YEAR) {
      return { value: s / SECONDS_PER_YEAR, unit: 'years' };
    }
    if (s >= SECONDS_PER_DAY) {
      return { value: s / SECONDS_PER_DAY, unit: 'days' };
    }
    if (s >= SECONDS_PER_HOUR) {
      return { value: s / SECONDS_PER_HOUR, unit: 'hours' };
    }
    if (s >= SECONDS_PER_MINUTE) {
      return { value: s / SECONDS_PER_MINUTE, unit: 'minutes' };
    }
    if (s >= 1) {
      return { value: s, unit: 's' };
    }
    if (s >= 1e-3) {
      return { value: s * 1e3, unit: 'ms' };
    }
    if (s >= 1e-6) {
      return { value: s * 1e6, unit: 'us' };
    }
    if (s >= 1e-9) {
      return { value: s * 1e9, unit: 'ns' };
    }
    if (s >= 1e-12) {
      return { value: s * 1e12, unit: 'ps' };
    }
    return { value: s, unit: 's' };
  }

  // Core computation.  Call only with validated input.
  function compute(p) {
    var period = 1 / p.fClk;
    var r = period - p.tCO - p.tSU;
    var missionSeconds = p.missionYears * SECONDS_PER_YEAR;

    var currentTmet = tMETFor(p.n, p.t0, r);
    var currentMTBF = mtbfSeconds(p.c1, p.c2, currentTmet, p.fClk, p.fData);

    var table = [];
    for (var n = 1; n <= 4; n += 1) {
      var tmet = tMETFor(n, p.t0, r);
      var mtbf = mtbfSeconds(p.c1, p.c2, tmet, p.fClk, p.fData);
      table.push({
        n: n,
        tMET: tmet,
        rTotal: tmet,
        mtbf: mtbf,
        scaled: scaleSeconds(mtbf)
      });
    }

    return {
      ok: true,
      period: period,
      r: r,
      tMET: currentTmet,
      mtbf: currentMTBF,
      scaled: scaleSeconds(currentMTBF),
      table: table,
      pass: currentMTBF >= missionSeconds,
      missionSeconds: missionSeconds,
      missionYears: p.missionYears,
      inputs: p
    };
  }

  // Invert the MTBF formula to solve for tMET given a target MTBF.
  // Useful for sanity checks and for finding the minimum N required.
  function tMETFromMTBF(c1, c2, fClk, fData, targetMTBF) {
    return Math.log(targetMTBF * c1 * fClk * fData) / c2;
  }

  // Find the smallest N (1..4) whose MTBF meets the mission, or null.
  function minPassingN(p) {
    var period = 1 / p.fClk;
    var r = period - p.tCO - p.tSU;
    var missionSeconds = p.missionYears * SECONDS_PER_YEAR;
    for (var n = 1; n <= 4; n += 1) {
      var tmet = tMETFor(n, p.t0, r);
      var mtbf = mtbfSeconds(p.c1, p.c2, tmet, p.fClk, p.fData);
      if (mtbf >= missionSeconds) {
        return n;
      }
    }
    return null;
  }

  function presetByName(name) {
    for (var i = 0; i < PRESETS.length; i += 1) {
      if (PRESETS[i].name === name) {
        return PRESETS[i];
      }
    }
    return null;
  }

  MTBF.validate = validate;
  MTBF.compute = compute;
  MTBF.scaleSeconds = scaleSeconds;
  MTBF.tMETFromMTBF = tMETFromMTBF;
  MTBF.minPassingN = minPassingN;
  MTBF.tMETFor = tMETFor;
  MTBF.mtbfSeconds = mtbfSeconds;
  MTBF.PRESETS = PRESETS;
  MTBF.DEFAULTS = DEFAULTS;
  MTBF.SECONDS_PER_YEAR = SECONDS_PER_YEAR;
})(MTBF);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = MTBF;
}
