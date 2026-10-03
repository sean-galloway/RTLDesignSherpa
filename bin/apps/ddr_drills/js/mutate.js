// mutate.js -- wrong-answer generation for the bank-state drill.
//
// DDRD.mutators is an ordered list of mutation functions. Each takes
// (cmds, ctx) and returns a NEW cmds array, or null when the mutation is
// not applicable to this schedule. ctx = {reqs, bankState, topo, opts,
// policy, rng}.
//
// Rules every mutator obeys:
//   - never mutates its input array (immutability)
//   - never removes, moves, or edits annotation Cmds (skip_turnaround is the
//     documented exception: it targets annotations, and its output is always
//     rejected by make_wrong_answers because the real-command subsequence is
//     unchanged -- a wrong answer that differs only in annotation text is
//     not a different schedule)
//   - the output should look like a plausible student error
//
// make_wrong_answers(correct, ctx) walks the mutator list in order, keeps
// each candidate only if it is textually distinct from the correct schedule
// and from all previously kept picks AND its real-command subsequence
// differs from the correct one, then falls back to swap_adjacent / drop_cmd,
// then to a bounded permutation guard. It returns exactly 3 wrongs or
// throws (the scenario test asserts it never throws for any generator).
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  function idx_first(cmds, pred) {
    for (var i = 0; i < cmds.length; i++) {
      if (pred(cmds[i])) {
        return i;
      }
    }
    return -1;
  }

  function without_index(cmds, i) {
    return cmds.slice(0, i).concat(cmds.slice(i + 1));
  }

  // skip_pre: drop the first PRE. The bank then has two rows "open" at
  // once -- the classic forgotten-precharge error.
  function skip_pre(cmds) {
    var i = idx_first(cmds, function (c) {
      return !c.annotation && c.type === 'PRE';
    });
    return i === -1 ? null : without_index(cmds, i);
  }

  // add_unnecessary_act: insert an ACT for a row that is already open,
  // right before a column command that was a page hit. Re-simulates the
  // schedule from the scenario's initial bank state to find a true hit.
  function add_unnecessary_act(cmds, ctx) {
    var state = ctx && ctx.bankState ? DDRD.clone_bank_state(ctx.bankState)
                                     : null;
    for (var i = 0; i < cmds.length; i++) {
      var c = cmds[i];
      if (c.annotation) {
        continue;
      }
      if (c.type === 'ACT') {
        if (state) {
          state[c.bank].openRow = c.row;
        }
      } else if (c.type === 'PRE') {
        if (state) {
          state[c.bank].openRow = null;
        }
      } else if (DDRD.is_col_cmd(c)) {
        var openRow = state ? state[c.bank].openRow : null;
        // A hit needs the row tracked by the ACT that fed this command.
        // When ctx has no bankState we conservatively treat every column
        // command as not-a-hit (mutation not applicable).
        if (openRow !== null) {
          var extra = DDRD.make_cmd('ACT', c.bank, openRow, null, c.sid);
          return cmds.slice(0, i).concat([extra], cmds.slice(i));
        }
      }
    }
    return null;
  }

  // skip_act: drop the first ACT. The column command then addresses a bank
  // that was never opened.
  function skip_act(cmds) {
    var i = idx_first(cmds, function (c) {
      return !c.annotation && c.type === 'ACT';
    });
    return i === -1 ? null : without_index(cmds, i);
  }

  // skip_turnaround: drop the first annotation. Output always fails the
  // real-subsequence distinctness check in make_wrong_answers; kept in the
  // list so the mutator catalog documents the concept.
  function skip_turnaround(cmds) {
    var i = idx_first(cmds, function (c) {
      return c.annotation === true;
    });
    return i === -1 ? null : without_index(cmds, i);
  }

  // serialize_acts: collapse a two-phase pipelined schedule back into
  // interleaved ACT/column pairs (the naive in-order schedule a student
  // writes before learning about ACT pipelining). Applicable only when the
  // schedule opens with a run of >= 2 consecutive ACTs (phase 1).
  function serialize_acts(cmds) {
    var nActs = 0;
    while (nActs < cmds.length && !cmds[nActs].annotation &&
           cmds[nActs].type === 'ACT') {
      nActs++;
    }
    if (nActs < 2) {
      return null;
    }
    var pending = cmds.slice(0, nActs);      // unclaimed phase-1 ACTs
    var rest = cmds.slice(nActs);
    var out = [];
    for (var i = 0; i < rest.length; i++) {
      var c = rest[i];
      if (DDRD.is_col_cmd(c)) {
        for (var a = 0; a < pending.length; a++) {
          if (pending[a].bank === c.bank) {
            out.push(pending[a]);
            pending.splice(a, 1);
            break;
          }
        }
      }
      out.push(c);
    }
    // Any ACT whose bank never got a column command trails at the end
    // (cannot happen for engine-produced pipelines, kept for safety).
    return out.concat(pending);
  }

  // reverse_rd_order: reverse the first maximal run of >= 2 consecutive
  // read-op column commands (RD or RDA). A plausible "data comes back in
  // request order" confusion. Annotations break runs.
  function reverse_rd_order(cmds) {
    var start = -1;
    var end = -1;
    for (var i = 0; i < cmds.length; i++) {
      var c = cmds[i];
      var isRd = DDRD.is_col_cmd(c) && DDRD.cmd_op(c) === 'RD';
      if (isRd) {
        if (start === -1) {
          start = i;
        }
        end = i;
      } else {
        if (start !== -1 && end - start >= 1) {
          break;
        }
        start = -1;
        end = -1;
      }
    }
    if (start === -1 || end - start < 1) {
      return null;
    }
    var run = cmds.slice(start, end + 1);
    // Reversing a run of textually identical commands is a no-op; refuse.
    if (DDRD.format_schedule(run) ===
        DDRD.format_schedule(run.slice().reverse())) {
      return null;
    }
    return cmds.slice(0, start).concat(run.slice().reverse(),
                                       cmds.slice(end + 1));
  }

  // wrong_policy: re-run the OTHER page policy on the same requests.
  // open <-> close; frfcfs degrades to plain open-page (pure FCFS order).
  function wrong_policy(cmds, ctx) {
    if (!ctx || !ctx.reqs || !ctx.bankState || !ctx.topo) {
      return null;
    }
    var other = ctx.policy === 'close' ? 'open' : 'close';
    if (ctx.policy === 'frfcfs') {
      other = 'open';
    }
    var result = DDRD.schedule_with_policy(other, ctx.reqs, ctx.bankState,
                                           ctx.topo, ctx.opts);
    return result.cmds;
  }

  // -- Fallbacks (used only when the mutator list yields < 3 keeps) ---------

  // swap_adjacent: swap the first pair of textually distinct, directly
  // adjacent column commands.
  function swap_adjacent(cmds) {
    for (var i = 0; i + 1 < cmds.length; i++) {
      var a = cmds[i];
      var b = cmds[i + 1];
      if (DDRD.is_col_cmd(a) && DDRD.is_col_cmd(b) &&
          DDRD.format_cmd(a) !== DDRD.format_cmd(b)) {
        var out = cmds.slice();
        out[i] = b;
        out[i + 1] = a;
        return out;
      }
    }
    return null;
  }

  // drop_cmd: drop one non-ACT real command (a column command first, else
  // a PRE). Simulates losing a request between queue and scheduler.
  function drop_cmd(cmds) {
    var i = idx_first(cmds, function (c) {
      return DDRD.is_col_cmd(c);
    });
    if (i === -1) {
      i = idx_first(cmds, function (c) {
        return !c.annotation && c.type === 'PRE';
      });
    }
    return i === -1 ? null : without_index(cmds, i);
  }

  DDRD.mutators = [
    skip_pre,
    add_unnecessary_act,
    skip_act,
    skip_turnaround,
    serialize_acts,
    reverse_rd_order,
    wrong_policy
  ];
  DDRD.mutator_names = [
    'skip_pre',
    'add_unnecessary_act',
    'skip_act',
    'skip_turnaround',
    'serialize_acts',
    'reverse_rd_order',
    'wrong_policy'
  ];
  DDRD.swap_adjacent = swap_adjacent;
  DDRD.drop_cmd = drop_cmd;

  // -- make_wrong_answers ----------------------------------------------------

  function real_key(cmds) {
    return DDRD.format_real(cmds);
  }

  function text_key(cmds) {
    return DDRD.format_schedule(cmds);
  }

  // Permutation guard: rebuild the schedule with column commands reordered
  // by pairwise swaps, then by seeded shuffles, until 3 unique wrongs exist
  // or the bound runs out. Throws only when truly impossible.
  function permutation_guard(correct, tryAdd, rng) {
    var colIdx = [];
    for (var i = 0; i < correct.length; i++) {
      if (DDRD.is_col_cmd(correct[i])) {
        colIdx.push(i);
      }
    }
    // Deterministic pairwise swaps first (stable across rng streams).
    for (var a = 0; a < colIdx.length; a++) {
      for (var b = a + 1; b < colIdx.length; b++) {
        var out = correct.slice();
        var tmp = out[colIdx[a]];
        out[colIdx[a]] = out[colIdx[b]];
        out[colIdx[b]] = tmp;
        if (tryAdd(out)) {
          return;
        }
      }
    }
    // Seeded shuffles of the column subsequence as a last resort.
    var rand = rng || DDRD.mulberry32(0xC0FFEE);
    for (var attempt = 0; attempt < 100; attempt++) {
      var perm = DDRD.rshuffle(rand, colIdx);
      var rebuilt = correct.slice();
      for (var k = 0; k < colIdx.length; k++) {
        rebuilt[colIdx[k]] = correct[perm[k]];
      }
      if (tryAdd(rebuilt)) {
        return;
      }
    }
  }

  // make_wrong_answers(correct, ctx) -> exactly 3 wrong schedules (arrays of
  // Cmd), each textually distinct from correct and from each other, and each
  // differing from correct in its real-command subsequence. Throws only if
  // truly impossible.
  function make_wrong_answers(correct, ctx) {
    var seenReal = {};
    var seenText = {};
    seenReal[real_key(correct)] = true;
    seenText[text_key(correct)] = true;
    var wrongs = [];

    function tryAdd(cand) {
      if (!cand) {
        return false;
      }
      var rk = real_key(cand);
      var tk = text_key(cand);
      if (seenReal[rk] || seenText[tk]) {
        return false;
      }
      seenReal[rk] = true;
      seenText[tk] = true;
      wrongs.push(cand);
      return wrongs.length >= 3;
    }

    for (var m = 0; m < DDRD.mutators.length; m++) {
      if (tryAdd(DDRD.mutators[m](correct, ctx || {}))) {
        return wrongs;
      }
    }
    if (tryAdd(swap_adjacent(correct))) {
      return wrongs;
    }
    if (tryAdd(drop_cmd(correct))) {
      return wrongs;
    }
    permutation_guard(correct, tryAdd, ctx && ctx.rng);

    if (wrongs.length < 3) {
      throw new Error('make_wrong_answers: only ' + wrongs.length +
                      ' distinct wrong schedules possible for:\n' +
                      text_key(correct));
    }
    return wrongs;
  }

  DDRD.make_wrong_answers = make_wrong_answers;
})(DDRD);
