// engine.js -- the tech-agnostic DRAM command schedulers. Three policies:
//   schedule_open_page   open-page (keep rows open; ACT pipelining when legal)
//   schedule_close_page  close-page (every column command auto-precharges)
//   schedule_fr_fcfs     one-level FR-FCFS reorder, then open-page
//
// Every scheduler returns {cmds, reasons, bankState}:
//   cmds      array of Cmd objects (including annotation Cmds)
//   reasons   one human-readable reason string per cmd, aligned by index
//   bankState the final bank state (input is cloned, never mutated)
//
// Turnaround rule: after emitting each column command, if its data-bus op
// differs from the previous COLUMN command's op -- globally, across banks,
// and through any PRE/ACT interlude -- a turnaround annotation is inserted
// immediately BEFORE the new column command: "(tWTR bubble)" on WR->RD,
// "(tRTW bubble)" on RD->WR. PRE and ACT never reset the previous-op latch.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  var DEFAULT_TURNAROUND = { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' };

  function turnaround_labels(opts) {
    var t = (opts && opts.turnaround) || {};
    return {
      wtr: t.wtr || DEFAULT_TURNAROUND.wtr,
      rtw: t.rtw || DEFAULT_TURNAROUND.rtw
    };
  }

  // Shared emitter: tracks the previous column op and inserts turnaround
  // annotations. Returns an object with push helpers so each scheduler only
  // describes its own command choices.
  function make_emitter(labels) {
    var cmds = [];
    var reasons = [];
    var prevColOp = null;

    function push(cmd, reason) {
      cmds.push(cmd);
      reasons.push(reason);
    }

    function push_act(bank, row, reason, sid) {
      push(DDRD.make_cmd('ACT', bank, row, null, sid), reason);
    }

    function push_pre(bank, reason, sid) {
      push(DDRD.make_cmd('PRE', bank, null, null, sid), reason);
    }

    // Emits a column command, inserting a turnaround annotation first when
    // the bus direction flips relative to the previous column command.
    function push_col(cmd, reason) {
      var op = DDRD.cmd_op(cmd);
      if (prevColOp !== null && op !== prevColOp) {
        if (prevColOp === 'WR') {
          push(DDRD.make_annotation(labels.wtr, 'WR->RD turnaround'),
               labels.wtr + ' -- WR->RD turnaround');
        } else {
          push(DDRD.make_annotation(labels.rtw, 'RD->WR turnaround'),
               labels.rtw + ' -- RD->WR turnaround');
        }
      }
      push(cmd, reason);
      prevColOp = op;
    }

    return {
      cmds: cmds,
      reasons: reasons,
      push_act: push_act,
      push_pre: push_pre,
      push_col: push_col
    };
  }

  function is_miss(state, req) {
    var open = state[req.bank].openRow;
    return open !== null && open !== req.row;
  }

  // schedule_open_page(reqs, bankState, topo, opts)
  //
  // Sequential per request:
  //   bank idle          -> ACT + column command
  //   bank open, hit     -> column command only
  //   bank open, miss    -> PRE, ACT, column command
  //
  // ACT pipelining engages ONLY when ALL THREE preconditions hold:
  //   1. every request has the same op
  //   2. every request targets a distinct bank
  //   3. zero page misses (no bank open on the wrong row)
  // and at least one ACT is needed (with zero ACTs the two-phase output is
  // textually identical to the sequential one, so the sequential path runs).
  // opts.pipelining === false forces the sequential path (the sandbox
  // exposes this as the "ACT pipelining" option box).
  // Phase 1 = all needed ACTs in request order; phase 2 = all column
  // commands in request order.
  function schedule_open_page(reqs, bankState, topo, opts) {
    var state = DDRD.clone_bank_state(bankState);
    var labels = turnaround_labels(opts);
    var em = make_emitter(labels);

    var pipeliningAllowed = !opts || opts.pipelining !== false;

    var sameOp = true;
    var seenBanks = {};
    var distinctBanks = true;
    var zeroMisses = true;
    var actsNeeded = 0;
    for (var i = 0; i < reqs.length; i++) {
      var r = reqs[i];
      if (i > 0 && r.op !== reqs[0].op) {
        sameOp = false;
      }
      if (seenBanks[r.bank]) {
        distinctBanks = false;
      }
      seenBanks[r.bank] = true;
      if (is_miss(state, r)) {
        zeroMisses = false;
      }
      if (state[r.bank].openRow === null) {
        actsNeeded++;
      }
    }

    var pipelined = pipeliningAllowed && reqs.length >= 2 && sameOp &&
                    distinctBanks && zeroMisses && actsNeeded >= 1;

    if (pipelined) {
      // Phase 1: every needed ACT, in request order.
      var actedBanks = {};
      for (var a = 0; a < reqs.length; a++) {
        var ra = reqs[a];
        if (state[ra.bank].openRow === null) {
          em.push_act(ra.bank, ra.row,
                      'ACT B' + ra.bank + ' R' + ra.row +
                      ' -- bank idle (pipelined ACT, phase 1)', ra.sid);
          state[ra.bank].openRow = ra.row;
          actedBanks[ra.bank] = true;
        }
      }
      // Phase 2: every column command, in request order. All ops are
      // identical, so no turnaround can fire here.
      for (var c = 0; c < reqs.length; c++) {
        var rc = reqs[c];
        em.push_col(DDRD.make_cmd(rc.op, rc.bank, null, rc.col, rc.sid),
                    rc.op + ' B' + rc.bank + ' C' + rc.col +
                    (actedBanks[rc.bank]
                       ? ' -- after ACT (pipelined, phase 2)'
                       : ' -- page hit (pipelined, phase 2)'));
      }
      return { cmds: em.cmds, reasons: em.reasons, bankState: state };
    }

    // Sequential path.
    for (var k = 0; k < reqs.length; k++) {
      var req = reqs[k];
      var entry = state[req.bank];
      var wasHit = entry.openRow === req.row;
      if (entry.openRow === null) {
        em.push_act(req.bank, req.row,
                    'ACT B' + req.bank + ' R' + req.row + ' -- bank idle',
                    req.sid);
        entry.openRow = req.row;
      } else if (entry.openRow !== req.row) {
        em.push_pre(req.bank,
                    'PRE B' + req.bank + ' -- row conflict (R' + entry.openRow +
                    ' open)', req.sid);
        em.push_act(req.bank, req.row,
                    'ACT B' + req.bank + ' R' + req.row +
                    ' -- page miss (R' + entry.openRow + ' open)', req.sid);
        entry.openRow = req.row;
      }
      em.push_col(DDRD.make_cmd(req.op, req.bank, null, req.col, req.sid),
                  req.op + ' B' + req.bank + ' C' + req.col +
                  (wasHit ? ' -- page hit' : ' -- after ACT'));
    }
    return { cmds: em.cmds, reasons: em.reasons, bankState: state };
  }

  // schedule_close_page(reqs, bankState, topo)
  //
  // Per request: (PRE if the bank is open) + ACT + RDA/WRA. Every column
  // command carries auto-precharge, so the bank ends idle. RDA/WRA are
  // column commands for turnaround purposes (RDA = read op, WRA = write
  // op); close-page uses the default turnaround labels (no opts param per
  // the engine contract -- recorded in notes/design.md).
  function schedule_close_page(reqs, bankState, topo) {
    var state = DDRD.clone_bank_state(bankState);
    var em = make_emitter(turnaround_labels(null));

    for (var i = 0; i < reqs.length; i++) {
      var req = reqs[i];
      var entry = state[req.bank];
      if (entry.openRow !== null) {
        em.push_pre(req.bank,
                    'PRE B' + req.bank + ' -- closing open row R' +
                    entry.openRow + ' (close-page policy)', req.sid);
        entry.openRow = null;
      }
      em.push_act(req.bank, req.row,
                  'ACT B' + req.bank + ' R' + req.row + ' -- close-page policy',
                  req.sid);
      var type = DDRD.col_type_for(req.op, 'close');
      var auto = req.op === 'RD' ? 'read with auto-precharge'
                                 : 'write with auto-precharge';
      em.push_col(DDRD.make_cmd(type, req.bank, null, req.col, req.sid),
                  type + ' B' + req.bank + ' C' + req.col + ' -- ' + auto);
      entry.openRow = null;
    }
    return { cmds: em.cmds, reasons: em.reasons, bankState: state };
  }

  // schedule_fr_fcfs(reqs, bankState, topo, opts)
  //
  // First-ready first-come-first-served, one-level reorder: scan arrival
  // order; the oldest page-hit may jump ahead of the oldest page miss
  // (ready = bank open on the requested row, judged against the INITIAL
  // bank state; idle banks count as not-ready). One hit jumps per scan
  // pass; passes repeat until no hit sits behind a miss. The reordered
  // list is then fed through the open-page scheduler.
  // Returns {cmds, reasons, bankState, reordered} so the UI can show
  // served-vs-arrival order.
  function schedule_fr_fcfs(reqs, bankState, topo, opts) {
    var initial = DDRD.clone_bank_state(bankState);

    function ready(req) {
      return initial[req.bank].openRow === req.row;
    }

    var order = reqs.slice();
    for (;;) {
      var missIdx = -1;
      for (var i = 0; i < order.length; i++) {
        if (!ready(order[i])) {
          missIdx = i;
          break;
        }
      }
      if (missIdx === -1) {
        break;
      }
      var hitIdx = -1;
      for (var j = missIdx + 1; j < order.length; j++) {
        if (ready(order[j])) {
          hitIdx = j;
          break;
        }
      }
      if (hitIdx === -1) {
        break;
      }
      var hit = order.splice(hitIdx, 1)[0];
      order.splice(missIdx, 0, hit);
    }

    var result = schedule_open_page(order, bankState, topo, opts);
    return {
      cmds: result.cmds,
      reasons: result.reasons,
      bankState: result.bankState,
      reordered: order
    };
  }

  // Runs whichever policy a scenario declares. Shared by scenario building
  // and the wrong_policy mutator.
  function schedule_with_policy(policy, reqs, bankState, topo, opts) {
    if (policy === 'close') {
      return schedule_close_page(reqs, bankState, topo);
    }
    if (policy === 'frfcfs') {
      return schedule_fr_fcfs(reqs, bankState, topo, opts);
    }
    return schedule_open_page(reqs, bankState, topo, opts);
  }

  DDRD.schedule_open_page = schedule_open_page;
  DDRD.schedule_close_page = schedule_close_page;
  DDRD.schedule_fr_fcfs = schedule_fr_fcfs;
  DDRD.schedule_with_policy = schedule_with_policy;
})(DDRD);
