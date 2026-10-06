// model.js -- Req/Cmd factories, bank-state helpers, and the canonical text
// formats used as dedup keys (format_cmd / format_req / format_schedule).
//
// A Req is a memory request to schedule:
//   {op: 'RD'|'WR', bank, row, col, sid?}
// A Cmd is one DRAM command (or an annotation) in a produced schedule:
//   {type: 'ACT'|'PRE'|'RD'|'WR'|'RDA'|'WRA', bank, row?, col?, sid?}
//   {annotation: true, text: '(tWTR bubble)', detail: 'WR->RD turnaround'}
//
// Annotation commands are first-class Cmd objects. They mark bus-direction
// turnaround bubbles in the schedule text. Mutators and any logic that
// reasons about real commands MUST skip them (see real_cmds below).
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  var COL_TYPES = { RD: true, WR: true, RDA: true, WRA: true };

  function make_req(op, bank, row, col, sid) {
    var req = { op: op, bank: bank, row: row, col: col };
    if (sid !== undefined && sid !== null) {
      req.sid = sid;
    }
    return req;
  }

  function make_cmd(type, bank, row, col, sid) {
    var cmd = { type: type, bank: bank };
    if (row !== undefined && row !== null) {
      cmd.row = row;
    }
    if (col !== undefined && col !== null) {
      cmd.col = col;
    }
    if (sid !== undefined && sid !== null) {
      cmd.sid = sid;
    }
    return cmd;
  }

  function make_annotation(text, detail) {
    return { annotation: true, text: text, detail: detail };
  }

  function is_col_cmd(cmd) {
    return !cmd.annotation && COL_TYPES[cmd.type] === true;
  }

  function is_real_cmd(cmd) {
    return !cmd.annotation;
  }

  // The data-bus operation a column command performs: RDA reads, WRA writes.
  // Used by the turnaround rule ("for turnaround purposes RDA counts as a
  // read op, WRA as a write op").
  function cmd_op(cmd) {
    if (cmd.type === 'RD' || cmd.type === 'RDA') {
      return 'RD';
    }
    if (cmd.type === 'WR' || cmd.type === 'WRA') {
      return 'WR';
    }
    return null;
  }

  // The column command type a request produces under a page policy.
  function col_type_for(op, policy) {
    if (policy === 'close') {
      return op === 'RD' ? 'RDA' : 'WRA';
    }
    return op;
  }

  // -- Bank state ------------------------------------------------------------
  // Bank state is an array of {openRow: int|null}, length topo.banks. It is
  // threaded through the schedulers; schedulers clone it and never mutate
  // the caller's array. With SID topologies the drill model indexes bank
  // state by bank number alone; SID generators never reuse a bank number
  // across SIDs (recorded in notes/design.md).

  function make_bank_state(topo) {
    var state = [];
    for (var b = 0; b < topo.banks; b++) {
      state.push({ openRow: null });
    }
    return state;
  }

  function clone_bank_state(state) {
    return state.map(function (entry) {
      return { openRow: entry.openRow };
    });
  }

  // bg(bank): bank group index, or null on topologies without bank groups.
  // When null, no group-scoped logic or annotations apply anywhere.
  function bg(topo, bank) {
    return topo.hasBankGroups ? Math.floor(bank / topo.banksPerGroup) : null;
  }

  // -- Canonical text formats ------------------------------------------------
  // These strings are the identity of a command/schedule: make_wrong_answers
  // dedups candidate wrong answers by them.

  // The artificial-geometry disclaimer shown at the top of every drill and
  // the sandbox. The drills run on a tiny on-purpose geometry so bank state
  // is visible at a glance; the rules practiced are identical to real parts.
  // Entity ranges are spelled out (BG0, BG1 / B0-B7 / R0-R7 / C0-C7) so the
  // labels used in questions and the sandbox need no separate decoding.
  function idRange(prefix, n) {
    return n > 1 ? prefix + '0-' + prefix + (n - 1) : prefix + '0';
  }

  function assumptionsText(topo) {
    var parts = [];
    if (topo.hasBankGroups) {
      var gids = [];
      for (var g = 0; g < topo.groups; g++) { gids.push('BG' + g); }
      parts.push(topo.groups + ' bank groups (' + gids.join(', ') + ')');
    }
    parts.push(topo.banks + ' banks (' + idRange('B', topo.banks) +
               (topo.hasBankGroups ? '' : ', no bank groups') + ')');
    parts.push(topo.rows + ' rows (' + idRange('R', topo.rows) + ')');
    parts.push(topo.cols + ' columns (' + idRange('C', topo.cols) + ')');
    var s = 'Artificial drill geometry: ' + parts.join(', ') +
            '. Real parts differ -- thousands of rows and columns, and ' +
            'often more banks or groups -- but the scheduling and timing ' +
            'rules are the same.';
    if (topo.sids > 0) {
      s += ' This geometry repeats per stack (SID).';
    }
    return s;
  }

  function fmt_sid(x) {
    return (x.sid !== undefined && x.sid !== null) ? 'S' + x.sid + ' ' : '';
  }

  function format_cmd(cmd) {
    if (cmd.annotation) {
      return '--- ' + cmd.text + ' ---';
    }
    switch (cmd.type) {
      case 'ACT':
        return 'ACT ' + fmt_sid(cmd) + 'B' + cmd.bank + ' R' + cmd.row;
      case 'PRE':
        return 'PRE ' + fmt_sid(cmd) + 'B' + cmd.bank;
      default:
        return cmd.type + ' ' + fmt_sid(cmd) + 'B' + cmd.bank + ' C' + cmd.col;
    }
  }

  function format_req(req) {
    return req.op + ' ' + fmt_sid(req) + 'B' + req.bank +
           ' R' + req.row + ' C' + req.col;
  }

  function format_schedule(cmds) {
    return cmds.map(format_cmd).join('\n');
  }

  // The subsequence of real (non-annotation) commands. This is the semantic
  // identity of a schedule: two schedules that differ only in annotations
  // are the same answer.
  function real_cmds(cmds) {
    return cmds.filter(is_real_cmd);
  }

  function format_real(cmds) {
    return format_schedule(real_cmds(cmds));
  }

  DDRD.make_req = make_req;
  DDRD.make_cmd = make_cmd;
  DDRD.make_annotation = make_annotation;
  DDRD.is_col_cmd = is_col_cmd;
  DDRD.is_real_cmd = is_real_cmd;
  DDRD.cmd_op = cmd_op;
  DDRD.col_type_for = col_type_for;
  DDRD.make_bank_state = make_bank_state;
  DDRD.clone_bank_state = clone_bank_state;
  DDRD.bg = bg;
  DDRD.assumptionsText = assumptionsText;
  DDRD.format_cmd = format_cmd;
  DDRD.format_req = format_req;
  DDRD.format_schedule = format_schedule;
  DDRD.real_cmds = real_cmds;
  DDRD.format_real = format_real;
})(DDRD);
