// test_engine.js -- golden schedules for all three schedulers on both a
// bank-group topology and a flat one. Registers its suite on
// globalThis.DDRD_TEST_SUITES; run_tests.js supplies the assertion kit.
var SUITES = (typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES ||
             ((typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES = []);

(function () {
  'use strict';

  var DDRD = globalThis.DDRD;

  function topoBG() {
    return { hasBankGroups: true, groups: 2, banksPerGroup: 4,
             banks: 8, rows: 8, cols: 8, sids: 2 };
  }

  function topoFlat() {
    return { hasBankGroups: false, banks: 8, rows: 8, cols: 8, sids: 0 };
  }

  function bothTopos() {
    return [['BG', topoBG()], ['flat', topoFlat()]];
  }

  function fmt(cmds) {
    return DDRD.format_schedule(cmds);
  }

  function req(op, b, r, c) {
    return DDRD.make_req(op, b, r, c);
  }

  function openAt(topo, bank, row) {
    var s = DDRD.make_bank_state(topo);
    s[bank].openRow = row;
    return s;
  }

  SUITES.push({
    name: 'engine',
    run: function (t) {

      // -- bg() derivation ------------------------------------------------
      t.eq(DDRD.bg(topoBG(), 0), 0, 'bg: bank 0 -> group 0');
      t.eq(DDRD.bg(topoBG(), 5), 1, 'bg: bank 5 -> group 1');
      t.eq(DDRD.bg(topoFlat(), 5), null, 'bg: flat topology -> null');

      // -- open-page: idle / hit / miss on both topologies ----------------
      bothTopos().forEach(function (pair) {
        var label = pair[0];
        var topo = pair[1];

        var idle = DDRD.schedule_open_page(
          [req('RD', 3, 5, 2)], DDRD.make_bank_state(topo), topo, null);
        t.eq(fmt(idle.cmds), 'ACT B3 R5\nRD B3 C2',
             label + ': open-page idle bank -> ACT + RD');
        t.deepEq(idle.reasons, ['ACT B3 R5 -- bank idle',
                                'RD B3 C2 -- after ACT'],
                 label + ': idle-bank reasons');
        t.eq(idle.bankState[3].openRow, 5,
             label + ': idle bank ends with row open');

        var hit = DDRD.schedule_open_page(
          [req('RD', 3, 5, 2)], openAt(topo, 3, 5), topo, null);
        t.eq(fmt(hit.cmds), 'RD B3 C2',
             label + ': open-page hit -> column command only');
        t.deepEq(hit.reasons, ['RD B3 C2 -- page hit'],
                 label + ': page-hit reason');

        var miss = DDRD.schedule_open_page(
          [req('RD', 3, 5, 2)], openAt(topo, 3, 2), topo, null);
        t.eq(fmt(miss.cmds), 'PRE B3\nACT B3 R5\nRD B3 C2',
             label + ': open-page miss -> PRE + ACT + RD');
        t.deepEq(miss.reasons,
                 ['PRE B3 -- row conflict (R2 open)',
                  'ACT B3 R5 -- page miss (R2 open)',
                  'RD B3 C2 -- after ACT'],
                 label + ': miss reasons name the conflicting row');
      });

      // -- ACT pipelining: golden two-phase order -------------------------
      bothTopos().forEach(function (pair) {
        var label = pair[0];
        var topo = pair[1];

        var piped = DDRD.schedule_open_page(
          [req('RD', 0, 1, 1), req('RD', 2, 3, 2), req('RD', 5, 0, 3)],
          DDRD.make_bank_state(topo), topo, null);
        t.eq(fmt(piped.cmds),
             'ACT B0 R1\nACT B2 R3\nACT B5 R0\n' +
             'RD B0 C1\nRD B2 C2\nRD B5 C3',
             label + ': pipelining = all ACTs (phase 1) then all columns');
        t.ok(piped.reasons[0].indexOf('phase 1') !== -1 &&
             piped.reasons[4].indexOf('phase 2') !== -1,
             label + ': pipelined reasons name the phases');

        // One genuine hit among the ACTs still pipelines (zero misses).
        var mixed = DDRD.schedule_open_page(
          [req('RD', 0, 1, 1), req('RD', 2, 3, 2), req('RD', 5, 0, 3)],
          openAt(topo, 2, 3), topo, null);
        t.eq(fmt(mixed.cmds),
             'ACT B0 R1\nACT B5 R0\nRD B0 C1\nRD B2 C2\nRD B5 C3',
             label + ': pipelining hoists needed ACTs above hits');
        t.eq(mixed.reasons[2], 'RD B0 C1 -- after ACT (pipelined, phase 2)',
             label + ': pipelined after-ACT reason');
        t.eq(mixed.reasons[3], 'RD B2 C2 -- page hit (pipelined, phase 2)',
             label + ': pipelined page-hit reason');

        // Exactly one ACT with all preconditions met still hoists.
        var one = DDRD.schedule_open_page(
          [req('RD', 0, 1, 0), req('RD', 1, 1, 1)],
          openAt(topo, 0, 1), topo, null);
        t.eq(fmt(one.cmds), 'ACT B1 R1\nRD B0 C0\nRD B1 C1',
             label + ': single needed ACT hoists above the hit');
      });

      // -- pipelining preconditions, each individually falsified ----------
      bothTopos().forEach(function (pair) {
        var label = pair[0];
        var topo = pair[1];

        // (1) not all same op
        var mixedOp = DDRD.schedule_open_page(
          [req('WR', 0, 1, 1), req('RD', 2, 3, 2), req('RD', 5, 0, 3)],
          DDRD.make_bank_state(topo), topo, null);
        t.eq(fmt(mixedOp.cmds),
             'ACT B0 R1\nWR B0 C1\nACT B2 R3\n--- (tWTR bubble) ---\n' +
             'RD B2 C2\nACT B5 R0\nRD B5 C3',
             label + ': mixed ops -> no pipelining, tWTR before the RD');

        // (2) banks not distinct (same op, zero misses)
        var dupBank = DDRD.schedule_open_page(
          [req('RD', 1, 2, 0), req('RD', 3, 4, 0), req('RD', 1, 2, 7)],
          DDRD.make_bank_state(topo), topo, null);
        t.eq(fmt(dupBank.cmds),
             'ACT B1 R2\nRD B1 C0\nACT B3 R4\nRD B3 C0\nRD B1 C7',
             label + ': repeated bank -> ACTs stay with their columns');

        // (3) a page miss exists (same op, distinct banks)
        var hasMiss = DDRD.schedule_open_page(
          [req('RD', 0, 1, 1), req('RD', 2, 5, 2)],
          openAt(topo, 2, 3), topo, null);
        t.eq(fmt(hasMiss.cmds),
             'ACT B0 R1\nRD B0 C1\nPRE B2\nACT B2 R5\nRD B2 C2',
             label + ': one miss -> no ACT hoisting at all');
      });

      // -- turnaround annotations -----------------------------------------
      bothTopos().forEach(function (pair) {
        var label = pair[0];
        var topo = pair[1];

        // WR->RD across banks (both hits).
        var wtr = DDRD.schedule_open_page(
          [req('WR', 1, 2, 0), req('RD', 4, 6, 1), req('RD', 1, 2, 2)],
          (function () {
            var s = DDRD.make_bank_state(topo);
            s[1].openRow = 2;
            s[4].openRow = 6;
            return s;
          })(), topo, null);
        t.eq(fmt(wtr.cmds),
             'WR B1 C0\n--- (tWTR bubble) ---\nRD B4 C1\nRD B1 C2',
             label + ': WR->RD inserts tWTR bubble, RD->RD does not');
        t.ok(wtr.reasons.indexOf('(tWTR bubble) -- WR->RD turnaround') !== -1,
             label + ': tWTR reason string');

        // RD->WR across banks (both hits).
        var rtw = DDRD.schedule_open_page(
          [req('RD', 1, 2, 5), req('WR', 4, 6, 1), req('WR', 1, 2, 2)],
          (function () {
            var s = DDRD.make_bank_state(topo);
            s[1].openRow = 2;
            s[4].openRow = 6;
            return s;
          })(), topo, null);
        t.eq(fmt(rtw.cmds),
             'RD B1 C5\n--- (tRTW bubble) ---\nWR B4 C1\nWR B1 C2',
             label + ': RD->WR inserts tRTW bubble, WR->WR does not');
        t.ok(rtw.reasons.indexOf('(tRTW bubble) -- RD->WR turnaround') !== -1,
             label + ': tRTW reason string');

        // Through a PRE/ACT interlude: PRE and ACT must NOT reset the
        // previous column op.
        var interlude = DDRD.schedule_open_page(
          [req('WR', 0, 1, 1), req('RD', 0, 3, 2)],
          openAt(topo, 0, 1), topo, null);
        t.eq(fmt(interlude.cmds),
             'WR B0 C1\nPRE B0\nACT B0 R3\n--- (tWTR bubble) ---\nRD B0 C2',
             label + ': turnaround survives a PRE/ACT interlude');

        var interludeBack = DDRD.schedule_open_page(
          [req('RD', 0, 1, 1), req('WR', 0, 3, 2)],
          openAt(topo, 0, 1), topo, null);
        t.eq(fmt(interludeBack.cmds),
             'RD B0 C1\nPRE B0\nACT B0 R3\n--- (tRTW bubble) ---\nWR B0 C2',
             label + ': tRTW survives a PRE/ACT interlude');

        // Same op throughout: no annotations at all.
        var calm = DDRD.schedule_open_page(
          [req('RD', 1, 2, 0), req('RD', 4, 6, 1), req('RD', 1, 2, 2)],
          (function () {
            var s = DDRD.make_bank_state(topo);
            s[1].openRow = 2;
            s[4].openRow = 6;
            return s;
          })(), topo, null);
        t.ok(calm.cmds.every(function (c) { return !c.annotation; }),
             label + ': same-op stream emits no annotations');

        // Custom labels via opts.turnaround.
        var custom = DDRD.schedule_open_page(
          [req('WR', 1, 2, 0), req('RD', 4, 6, 1)],
          (function () {
            var s = DDRD.make_bank_state(topo);
            s[1].openRow = 2;
            s[4].openRow = 6;
            return s;
          })(), topo,
          { turnaround: { wtr: '(WTR!)', rtw: '(RTW!)' } });
        t.eq(fmt(custom.cmds), 'WR B1 C0\n--- (WTR!) ---\nRD B4 C1',
             label + ': opts.turnaround overrides the bubble label');
        t.ok(custom.reasons.indexOf('(WTR!) -- WR->RD turnaround') !== -1,
             label + ': custom label appears in the reason');
      });

      // -- close-page -------------------------------------------------------
      bothTopos().forEach(function (pair) {
        var label = pair[0];
        var topo = pair[1];

        // Bank open (even on the right row): PRE + ACT + RDA, ends idle.
        var openBank = DDRD.schedule_close_page(
          [req('RD', 3, 5, 2)], openAt(topo, 3, 5), topo);
        t.eq(fmt(openBank.cmds), 'PRE B3\nACT B3 R5\nRDA B3 C2',
             label + ': close-page precharges any open bank first');
        t.deepEq(openBank.reasons,
                 ['PRE B3 -- closing open row R5 (close-page policy)',
                  'ACT B3 R5 -- close-page policy',
                  'RDA B3 C2 -- read with auto-precharge'],
                 label + ': close-page reasons');
        t.eq(openBank.bankState[3].openRow, null,
             label + ': close-page bank ends idle');

        // Idle bank, write: ACT + WRA, ends idle.
        var idleWr = DDRD.schedule_close_page(
          [req('WR', 5, 6, 0)], DDRD.make_bank_state(topo), topo);
        t.eq(fmt(idleWr.cmds), 'ACT B5 R6\nWRA B5 C0',
             label + ': close-page write uses WRA');
        t.eq(idleWr.bankState[5].openRow, null,
             label + ': close-page write ends idle');

        // RDA/WRA are column commands for turnaround purposes.
        var turn = DDRD.schedule_close_page(
          [req('RD', 3, 2, 1), req('WR', 5, 6, 0)],
          DDRD.make_bank_state(topo), topo);
        t.eq(fmt(turn.cmds),
             'ACT B3 R2\nRDA B3 C1\nACT B5 R6\n--- (tRTW bubble) ---\n' +
             'WRA B5 C0',
             label + ': close-page RDA->WRA inserts tRTW bubble');

        var turnBack = DDRD.schedule_close_page(
          [req('WR', 3, 2, 1), req('RD', 5, 6, 0)],
          DDRD.make_bank_state(topo), topo);
        t.eq(fmt(turnBack.cmds),
             'ACT B3 R2\nWRA B3 C1\nACT B5 R6\n--- (tWTR bubble) ---\n' +
             'RDA B5 C0',
             label + ': close-page WRA->RDA inserts tWTR bubble');
      });

      // -- FR-FCFS ----------------------------------------------------------
      bothTopos().forEach(function (pair) {
        var label = pair[0];
        var topo = pair[1];

        // The oldest hit jumps ahead of the oldest miss.
        var reqs = [req('RD', 3, 2, 0), req('RD', 1, 4, 0),
                    req('RD', 3, 5, 7)];
        var r = DDRD.schedule_fr_fcfs(reqs, openAt(topo, 3, 5), topo, null);
        t.ok(r.reordered[0] === reqs[2] && r.reordered[1] === reqs[0] &&
             r.reordered[2] === reqs[1],
             label + ': fr_fcfs reordered = hit, miss, idle');
        t.eq(fmt(r.cmds),
             'RD B3 C7\nPRE B3\nACT B3 R2\nRD B3 C0\nACT B1 R4\nRD B1 C0',
             label + ': fr_fcfs serves the hit while the row is open');

        // Nothing ready behind the miss: arrival order preserved.
        var noHits = DDRD.schedule_fr_fcfs(
          [req('RD', 0, 3, 0), req('RD', 1, 4, 0)],
          (function () {
            var s = DDRD.make_bank_state(topo);
            s[0].openRow = 1;
            s[1].openRow = 2;
            return s;
          })(), topo, null);
        t.deepEq(noHits.reordered.map(DDRD.format_req),
                 ['RD B0 R3 C0', 'RD B1 R4 C0'],
                 label + ': fr_fcfs with no ready hit keeps arrival order');

        // All ready: nothing to reorder.
        var allReady = DDRD.schedule_fr_fcfs(
          [req('RD', 0, 1, 0), req('RD', 1, 2, 0)],
          (function () {
            var s = DDRD.make_bank_state(topo);
            s[0].openRow = 1;
            s[1].openRow = 2;
            return s;
          })(), topo, null);
        t.deepEq(allReady.reordered.map(DDRD.format_req),
                 ['RD B0 R1 C0', 'RD B1 R2 C0'],
                 label + ': fr_fcfs with all hits keeps arrival order');
      });

      // -- cross-cutting ----------------------------------------------------
      bothTopos().forEach(function (pair) {
        var label = pair[0];
        var topo = pair[1];

        // reasons are aligned 1:1 with cmds on every scheduler.
        var reqs = [req('WR', 0, 1, 0), req('RD', 2, 5, 1)];
        var st = DDRD.make_bank_state(topo);
        st[2].openRow = 3;
        var r1 = DDRD.schedule_open_page(reqs, st, topo, null);
        t.eq(r1.reasons.length, r1.cmds.length,
             label + ': open-page reasons aligned with cmds');
        var r2 = DDRD.schedule_close_page(reqs, st, topo);
        t.eq(r2.reasons.length, r2.cmds.length,
             label + ': close-page reasons aligned with cmds');
        var r3 = DDRD.schedule_fr_fcfs(reqs, st, topo, null);
        t.eq(r3.reasons.length, r3.cmds.length,
             label + ': fr_fcfs reasons aligned with cmds');

        // schedulers never mutate the caller's bank state.
        var frozen = DDRD.make_bank_state(topo);
        frozen[3].openRow = 2;
        DDRD.schedule_open_page([req('RD', 3, 5, 2)], frozen, topo, null);
        t.eq(frozen[3].openRow, 2,
             label + ': input bank state not mutated (immutability)');
      });
    }
  });
})();
