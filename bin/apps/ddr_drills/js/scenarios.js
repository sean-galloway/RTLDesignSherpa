// scenarios.js -- the 19 parameterized scenario generators for the
// bank-state drill, plus the filter/build API.
//
// Each generator: {id, tier, tags, requires, generate(topo, rng)} where
//   requires: {bankGroups: true?, sids: n?} -- topology features the
//             scenario needs; unmet requires exclude the generator outright
//   generate(topo, rng) -> {reqs, bankState, policy, explanation}
// All randomness flows through the rng parameter; generators never call
// Math.random(). Every address is bounded by the topology passed in.
//
// availableGenerators(topo) filters by requires. buildScenario(gen, topo,
// policyDefault, rng) runs the generator, computes the correct schedule
// under the declared policy, derives exactly 3 wrong answers via
// make_wrong_answers, and returns the full Scenario object with 4
// UNshuffled options (index 0 correct; shuffling is the UI's job).
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  // -- generation helpers ----------------------------------------------------

  function all_banks(topo) {
    var out = [];
    for (var b = 0; b < topo.banks; b++) {
      out.push(b);
    }
    return out;
  }

  function group_banks(topo, g) {
    var out = [];
    var start = g * topo.banksPerGroup;
    for (var b = start; b < start + topo.banksPerGroup; b++) {
      out.push(b);
    }
    return out;
  }

  // n distinct banks drawn from `pool` (defaults to all banks).
  function pick_banks(rng, topo, n, pool) {
    return DDRD.rshuffle(rng, pool || all_banks(topo)).slice(0, n);
  }

  function rrow(rng, topo) {
    return DDRD.rint(rng, 0, topo.rows - 1);
  }

  function rcol(rng, topo) {
    return DDRD.rint(rng, 0, topo.cols - 1);
  }

  // A row different from `avoid` (topo.rows must be >= 2; drill model has 8).
  function rrow_avoid(rng, topo, avoid) {
    var r;
    do {
      r = rrow(rng, topo);
    } while (r === avoid);
    return r;
  }

  // Bank state with given {bank, row} entries open, rest idle.
  function open_state(topo, entries) {
    var state = DDRD.make_bank_state(topo);
    for (var i = 0; i < entries.length; i++) {
      state[entries[i].bank].openRow = entries[i].row;
    }
    return state;
  }

  function scenario(reqs, bankState, policy, explanation) {
    return {
      reqs: reqs,
      bankState: bankState,
      policy: policy,
      explanation: explanation
    };
  }

  // -- the 19 generators -----------------------------------------------------

  var generators = [

    // == Tier 1: fundamentals ============================================

    {
      id: 'empty_page_sequential',
      tier: 1,
      tags: ['basics', 'open-page', 'act'],
      requires: {},
      generate: function (topo, rng) {
        var n = DDRD.rint(rng, 3, 4);
        var op = DDRD.rpick(rng, ['RD', 'WR']);
        var banks = pick_banks(rng, topo, n);
        var reqs = banks.map(function (b) {
          return DDRD.make_req(op, b, rrow(rng, topo), rcol(rng, topo));
        });
        var noun = op === 'RD' ? 'reads' : 'writes';
        return scenario(reqs, DDRD.make_bank_state(topo), 'open',
          'Every bank starts idle, so each request pays an ACT before its ' +
          'column command. Because all ' + n + ' ' + noun + ' target ' +
          'distinct banks with no row conflicts, the controller front-loads ' +
          'every ACT (phase 1) and then issues the ' + op + 's (phase 2): ' +
          'each later activate hides behind the earlier banks\' tRCD instead ' +
          'of stalling the data bus.');
      }
    },

    {
      id: 'page_hit_stream',
      tier: 1,
      tags: ['basics', 'hits', 'tCCD'],
      requires: {},
      generate: function (topo, rng) {
        var bank = DDRD.rint(rng, 0, topo.banks - 1);
        var row = rrow(rng, topo);
        var op = DDRD.rpick(rng, ['RD', 'WR']);
        var n = DDRD.rint(rng, 3, 4);
        var cols = DDRD.rshuffle(rng, (function () {
          var cs = [];
          for (var c = 0; c < topo.cols; c++) {
            cs.push(c);
          }
          return cs;
        })()).slice(0, n);
        var reqs = cols.map(function (c) {
          return DDRD.make_req(op, bank, row, c);
        });
        return scenario(reqs, open_state(topo, [{ bank: bank, row: row }]),
          'open',
          'B' + bank + ' already has R' + row + ' open, so every request is ' +
          'a page hit: no ACT, no PRE, just column commands spaced by tCCD. ' +
          'Each burst occupies BL/2 clocks of the DQ bus; back-to-back ' +
          'same-direction bursts at that spacing saturate it. This is the ' +
          'throughput ceiling every other scenario falls short of.');
      }
    },

    {
      id: 'single_page_miss',
      tier: 1,
      tags: ['basics', 'miss', 'pre'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 2);
        var rowOld = rrow(rng, topo);
        var rowNew = rrow_avoid(rng, topo, rowOld);
        var row2 = rrow(rng, topo);
        var op = DDRD.rpick(rng, ['RD', 'WR']);
        var reqs = [
          DDRD.make_req(op, banks[0], rowNew, rcol(rng, topo)),
          DDRD.make_req(op, banks[0], rowNew, rcol(rng, topo)),
          DDRD.make_req(op, banks[1], row2, rcol(rng, topo))
        ];
        return scenario(reqs,
          open_state(topo, [{ bank: banks[0], row: rowOld },
                            { bank: banks[1], row: row2 }]),
          'open',
          'B' + banks[0] + ' has R' + rowOld + ' open but the request wants ' +
          'R' + rowNew + ': a page miss. The controller must PRE the old ' +
          'row, ACT the new one, and only then issue the column command -- ' +
          'three commands where a hit costs one. The follow-up request to ' +
          'the now-open row, and the request to B' + banks[1] + ' whose row ' +
          'is already open, are plain hits.');
      }
    },

    {
      id: 'close_page_basics',
      tier: 1,
      tags: ['basics', 'close-page', 'auto-precharge'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 2);
        var rowA = rrow(rng, topo);
        var rowB = rrow(rng, topo);
        var reqs = [
          DDRD.make_req('RD', banks[0], rowA, rcol(rng, topo)),
          DDRD.make_req('WR', banks[1], rowB, rcol(rng, topo)),
          DDRD.make_req('RD', banks[0], rowA, rcol(rng, topo))
        ];
        return scenario(reqs, DDRD.make_bank_state(topo), 'close',
          'Close-page policy: every column command carries auto-precharge ' +
          '(RD becomes RDA, WR becomes WRA), so each bank returns to idle ' +
          'after one access. Even the return visit to B' + banks[0] + ' R' +
          rowA + ' -- the very same row -- pays a fresh ACT. Streaming ' +
          'traffic with no row locality likes this; anything with locality ' +
          'bleeds activates. Note the RD->WR direction change still costs a ' +
          'turnaround bubble.');
      }
    },

    // == Tier 2: one new idea ============================================

    {
      id: 'cross_group_streams',
      tier: 2,
      tags: ['bank-groups', 'tCCD', 'streams'],
      requires: { bankGroups: true },
      generate: function (topo, rng) {
        var gA = 0;
        var gB = Math.min(1, topo.groups - 1);
        var a = pick_banks(rng, topo, 2, group_banks(topo, gA));
        var b = pick_banks(rng, topo, 2, group_banks(topo, gB));
        var rows = [rrow(rng, topo), rrow(rng, topo),
                    rrow(rng, topo), rrow(rng, topo)];
        var order = [a[0], b[0], a[1], b[1]];
        var reqs = order.map(function (bank, i) {
          return DDRD.make_req('RD', bank, rows[i], rcol(rng, topo));
        });
        return scenario(reqs,
          open_state(topo, order.map(function (bank, i) {
            return { bank: bank, row: rows[i] };
          })),
          'open',
          'Two read streams interleaved across bank groups: B' + a[0] +
          '/B' + a[1] + ' sit in group ' + gA + ', B' + b[0] + '/B' + b[1] +
          ' in group ' + gB + '. Every access is a page hit, so the whole ' +
          'schedule is column commands -- and consecutive reads landing in ' +
          'DIFFERENT groups space by the short tCCDS, where same-group ' +
          'neighbors would pay tCCDL. Steering streams across groups is ' +
          'free bandwidth on a shared DQ bus.');
      }
    },

    {
      id: 'act_pipelining',
      tier: 2,
      tags: ['pipelining', 'act', 'tRCD'],
      requires: {},
      generate: function (topo, rng) {
        var op = DDRD.rpick(rng, ['RD', 'WR']);
        var banks;
        var explanation;
        if (topo.hasBankGroups) {
          var gA = 0;
          var gB = Math.min(1, topo.groups - 1);
          banks = pick_banks(rng, topo, 2, group_banks(topo, gA))
            .concat(pick_banks(rng, topo, 2, group_banks(topo, gB)));
          banks = DDRD.rshuffle(rng, banks);
          explanation =
            'Four ' + op + 's to four idle banks, two in each bank group. ' +
            'The controller issues all four ACTs first (phase 1), then the ' +
            'four column commands (phase 2): each ACT\'s tRCD hides behind ' +
            'the previous banks\' work, and ACTs landing in different ' +
            'groups space by the short tRRDS -- exactly why the bank picks ' +
            'straddle groups ' + gA + ' and ' + gB + '. Phase 2 then ' +
            'streams data back-to-back.';
        } else {
          banks = pick_banks(rng, topo, 4);
          explanation =
            'Four ' + op + 's to four idle banks. The controller issues ' +
            'all four ACTs first (phase 1), then the four column commands ' +
            '(phase 2): each ACT\'s tRCD hides behind the previous banks\' ' +
            'work. With no bank groups every ACT pair pays the same tRRD, ' +
            'and all four activates count toward one tFAW window -- the ' +
            'four-activate limit exactly, so the pipeline just fits.';
        }
        var reqs = banks.map(function (bank) {
          return DDRD.make_req(op, bank, rrow(rng, topo), rcol(rng, topo));
        });
        return scenario(reqs, DDRD.make_bank_state(topo), 'open',
          explanation);
      }
    },

    {
      id: 'twtr_turnaround',
      tier: 2,
      tags: ['turnaround', 'tWTR'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 2);
        var rowW = rrow(rng, topo);
        var rowR = rrow(rng, topo);
        var reqs = [
          DDRD.make_req('WR', banks[0], rowW, rcol(rng, topo)),
          DDRD.make_req('RD', banks[1], rowR, rcol(rng, topo)),
          DDRD.make_req('RD', banks[0], rowW, rcol(rng, topo))
        ];
        return scenario(reqs,
          open_state(topo, [{ bank: banks[0], row: rowW },
                            { bank: banks[1], row: rowR }]),
          'open',
          'A write followed by a read: the shared DQ bus must change ' +
          'direction, and write-to-read is the expensive turn. The last ' +
          'write data has to travel from the input buffer into the sense ' +
          'amps before a read may reuse them (tWTR) -- invisible on the ' +
          'bus, but enforced as command spacing. The final read runs ' +
          'back-to-back with the previous one: same direction costs only ' +
          'tCCD.');
      }
    },

    {
      id: 'trtw_turnaround',
      tier: 2,
      tags: ['turnaround', 'tRTW'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 2);
        var rowR = rrow(rng, topo);
        var rowW = rrow(rng, topo);
        var reqs = [
          DDRD.make_req('RD', banks[0], rowR, rcol(rng, topo)),
          DDRD.make_req('WR', banks[1], rowW, rcol(rng, topo)),
          DDRD.make_req('WR', banks[0], rowR, rcol(rng, topo))
        ];
        return scenario(reqs,
          open_state(topo, [{ bank: banks[0], row: rowR },
                            { bank: banks[1], row: rowW }]),
          'open',
          'A read followed by a write: the read burst and its postamble ' +
          'must clear the DQ bus before the write preamble (tRTW = BL/2 + ' +
          '2 clocks). Cheaper than the write-to-read case, but still a ' +
          'bubble -- grouping reads with reads and writes with writes is ' +
          'the single biggest bandwidth lever in mixed traffic. The second ' +
          'write follows the first with only tCCD between them.');
      }
    },

    {
      id: 'mixed_open_close_compare',
      tier: 2,
      tags: ['policy', 'compare', 'locality'],
      requires: {},
      generate: function (topo, rng) {
        var bank = DDRD.rint(rng, 0, topo.banks - 1);
        var row = rrow(rng, topo);
        var policy = DDRD.rpick(rng, ['open', 'close']);
        var cols = DDRD.rshuffle(rng, (function () {
          var cs = [];
          for (var c = 0; c < topo.cols; c++) {
            cs.push(c);
          }
          return cs;
        })()).slice(0, 3);
        var reqs = [
          DDRD.make_req('RD', bank, row, cols[0]),
          DDRD.make_req('RD', bank, row, cols[1]),
          DDRD.make_req('WR', bank, row, cols[2])
        ];
        var explanation;
        if (policy === 'open') {
          explanation =
            'Three requests to one row of B' + bank + ', and the open-page ' +
            'policy is in force: the first ACT opens the row, the next two ' +
            'requests are page hits, and only the RD->WR direction change ' +
            'costs a turnaround bubble. Under close-page every one of ' +
            'these would re-activate (RDA/WRA auto-precharge) -- one of the ' +
            'wrong answers shows exactly that schedule; compare them.';
        } else {
          explanation =
            'Three requests to one row of B' + bank + ', and the ' +
            'close-page policy is in force: every column command ' +
            'auto-precharges (RDA/WRA), so each request pays a fresh ACT ' +
            'and row locality buys nothing. Under open-page the second ' +
            'and third requests would be page hits -- one of the wrong ' +
            'answers shows that schedule; compare what locality saves.';
        }
        return scenario(reqs, DDRD.make_bank_state(topo), policy,
          explanation);
      }
    },

    {
      id: 'interleave_banks',
      tier: 2,
      tags: ['interleave', 'open-page', 'tRCD'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 2);
        var rowA = rrow(rng, topo);
        var rowB = rrow(rng, topo);
        var op = DDRD.rpick(rng, ['RD', 'WR']);
        var reqs = [
          DDRD.make_req(op, banks[0], rowA, rcol(rng, topo)),
          DDRD.make_req(op, banks[1], rowB, rcol(rng, topo)),
          DDRD.make_req(op, banks[0], rowA, rcol(rng, topo)),
          DDRD.make_req(op, banks[1], rowB, rcol(rng, topo))
        ];
        return scenario(reqs, DDRD.make_bank_state(topo), 'open',
          'Two request streams interleaved across two banks. The ACT to ' +
          'B' + banks[1] + ' hides behind B' + banks[0] + '\'s first ' +
          'burst (tRCD overlap), and the open-page policy keeps both rows ' +
          'resident, so the second visit to each bank is a page hit. Bank ' +
          'interleaving turns serial row misses into overlapped work.');
      }
    },

    {
      id: 'tfaw_window',
      tier: 2,
      tags: ['tFAW', 'act', 'timing'],
      requires: {},
      generate: function (topo, rng) {
        var op = DDRD.rpick(rng, ['RD', 'WR']);
        var banks = pick_banks(rng, topo, 5);
        var reqs = banks.map(function (bank) {
          return DDRD.make_req(op, bank, rrow(rng, topo), rcol(rng, topo));
        });
        return scenario(reqs, DDRD.make_bank_state(topo), 'open',
          'Five ' + op + 's to five idle banks means five activates ' +
          'queued back-to-back. tFAW allows only four ACTs per rolling ' +
          'window, so the fifth ACT stalls even though its bank is free ' +
          '-- with only 8 banks in this model the four-activate window ' +
          'can bind before tRRD does. The pipeline is still the right ' +
          'shape: front-load the ACTs, then stream the column commands.');
      }
    },

    {
      id: 'sid_pair_streams',
      tier: 2,
      tags: ['sid', 'streams', 'tCCDR'],
      requires: { sids: 2 },
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 2);
        var rowA = rrow(rng, topo);
        var rowB = rrow(rng, topo);
        var reqs = [
          DDRD.make_req('RD', banks[0], rowA, rcol(rng, topo), 0),
          DDRD.make_req('RD', banks[1], rowB, rcol(rng, topo), 1),
          DDRD.make_req('RD', banks[0], rowA, rcol(rng, topo), 0),
          DDRD.make_req('RD', banks[1], rowB, rcol(rng, topo), 1)
        ];
        return scenario(reqs,
          open_state(topo, [{ bank: banks[0], row: rowA },
                            { bank: banks[1], row: rowB }]),
          'open',
          'Two read streams on different stack IDs: SID bits behave as ' +
          'extra bank-address bits, so the two streams never share a ' +
          'bank, and every request here is a page hit. Reads that cross ' +
          'a stack boundary space by tCCDR -- longer than same-stack ' +
          'tCCDS -- because the data path crosses dies. Each pseudo ' +
          'channel still counts its array timings independently.');
      }
    },

    {
      id: 'hit_miss_mix',
      tier: 2,
      tags: ['hits', 'misses', 'locality'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 3);
        var rowHit = rrow(rng, topo);
        var rowOld = rrow(rng, topo);
        var rowNew = rrow_avoid(rng, topo, rowOld);
        var rowIdle = rrow(rng, topo);
        var op = DDRD.rpick(rng, ['RD', 'WR']);
        var reqs = [
          DDRD.make_req(op, banks[0], rowHit, rcol(rng, topo)),
          DDRD.make_req(op, banks[1], rowNew, rcol(rng, topo)),
          DDRD.make_req(op, banks[0], rowHit, rcol(rng, topo)),
          DDRD.make_req(op, banks[2], rowIdle, rcol(rng, topo))
        ];
        return scenario(reqs,
          open_state(topo, [{ bank: banks[0], row: rowHit },
                            { bank: banks[1], row: rowOld }]),
          'open',
          'One arrival stream, three outcomes: a page hit costs one ' +
          'command (B' + banks[0] + '), an empty bank costs two (B' +
          banks[2] + ': ACT + column), a wrong row costs three (B' +
          banks[1] + ': PRE + ACT + column). Nothing reorders here -- ' +
          'the spread in cost is pure row locality.');
      }
    },

    // == Tier 3: composed reasoning =======================================

    {
      id: 'frfcfs_basic',
      tier: 3,
      tags: ['frfcfs', 'reorder'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 2);
        var rowOpen = rrow(rng, topo);
        var rowWant = rrow_avoid(rng, topo, rowOpen);
        var rowOther = rrow(rng, topo);
        var reqs = [
          DDRD.make_req('RD', banks[0], rowWant, rcol(rng, topo)),
          DDRD.make_req('RD', banks[1], rowOther, rcol(rng, topo)),
          DDRD.make_req('RD', banks[0], rowOpen, rcol(rng, topo))
        ];
        return scenario(reqs,
          open_state(topo, [{ bank: banks[0], row: rowOpen }]),
          'frfcfs',
          'FR-FCFS serves the oldest READY request first: the hit on B' +
          banks[0] + ' R' + rowOpen + ' jumps ahead of the row conflict ' +
          'at the head of the queue. Arrival order would PRE the open ' +
          'row, serve the conflict, then re-open R' + rowOpen + ' for the ' +
          'last request -- two extra row cycles. First-ready serves the ' +
          'hit while the row is still open, then pays one PRE/ACT for ' +
          'the conflict.');
      }
    },

    {
      id: 'frfcfs_vs_fcfs_compare',
      tier: 3,
      tags: ['frfcfs', 'compare', 'reorder'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 3);
        var rowOpen = rrow(rng, topo);
        var rowWant = rrow_avoid(rng, topo, rowOpen);
        var rowB = rrow(rng, topo);
        var rowC = rrow(rng, topo);
        var reqs = [
          DDRD.make_req('RD', banks[0], rowWant, rcol(rng, topo)),
          DDRD.make_req('RD', banks[1], rowB, rcol(rng, topo)),
          DDRD.make_req('RD', banks[0], rowOpen, rcol(rng, topo)),
          DDRD.make_req('RD', banks[2], rowC, rcol(rng, topo))
        ];
        return scenario(reqs,
          open_state(topo, [{ bank: banks[0], row: rowOpen },
                            { bank: banks[1], row: rowB }]),
          'frfcfs',
          'Arrival order versus served order is the whole lesson. Pure ' +
          'FCFS takes the row conflict on B' + banks[0] + ' first, ' +
          'closing R' + rowOpen + ' -- and the third request then misses ' +
          'the row it could have hit: nine commands in all. FR-FCFS lets ' +
          'both ready hits jump the conflict (served order 2-3-1-4): ' +
          'seven commands for the same four requests. The reorder is one ' +
          'level deep, so it never starves the miss.');
      }
    },

    {
      id: 'tccdr_sid_spacing',
      tier: 3,
      tags: ['sid', 'tCCDR', 'timing'],
      requires: { sids: 2 },
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 2);
        var rowA = rrow(rng, topo);
        var rowB = rrow(rng, topo);
        var reqs = [
          DDRD.make_req('RD', banks[0], rowA, rcol(rng, topo), 0),
          DDRD.make_req('RD', banks[1], rowB, rcol(rng, topo), 1),
          DDRD.make_req('RD', banks[0], rowA, rcol(rng, topo), 0),
          DDRD.make_req('RD', banks[1], rowB, rcol(rng, topo), 1)
        ];
        return scenario(reqs,
          open_state(topo, [{ bank: banks[0], row: rowA },
                            { bank: banks[1], row: rowB }]),
          'open',
          'Back-to-back reads alternating across stack IDs. Within one ' +
          'stack, read-to-read spacing is tCCDS across groups or tCCDL ' +
          'inside one; crossing a stack boundary pays tCCDR, the longest ' +
          'of the three, because the read data path crosses die ' +
          'boundaries. On tall stacks, plan streams so SID crossings ' +
          'are rare.');
      }
    },

    {
      id: 'cross_group_turnaround',
      tier: 3,
      tags: ['turnaround', 'bank-groups', 'tWTR'],
      requires: { bankGroups: true },
      generate: function (topo, rng) {
        var gA = 0;
        var gB = Math.min(1, topo.groups - 1);
        var a = pick_banks(rng, topo, 2, group_banks(topo, gA));
        var b = pick_banks(rng, topo, 1, group_banks(topo, gB));
        var rowW = rrow(rng, topo);
        var rowR = rrow(rng, topo);
        var rowR2 = rrow(rng, topo);
        var reqs = [
          DDRD.make_req('WR', a[0], rowW, rcol(rng, topo)),
          DDRD.make_req('RD', b[0], rowR, rcol(rng, topo)),
          DDRD.make_req('RD', a[1], rowR2, rcol(rng, topo))
        ];
        return scenario(reqs,
          open_state(topo, [{ bank: a[0], row: rowW },
                            { bank: b[0], row: rowR },
                            { bank: a[1], row: rowR2 }]),
          'open',
          'The write lands in group ' + gA + ' and the read that follows ' +
          'it in group ' + gB + ': the internal write-to-read recovery ' +
          'uses the SHORT tWTRS because the banks sit in different groups ' +
          '(same group would pay tWTRL) -- but the DQ bus still turns ' +
          'around, so the (tWTR bubble) appears in the schedule. Group ' +
          'placement picks the internal parameter; the direction change ' +
          'owns the bus bubble. The final read pairs with the previous ' +
          'one at plain tCCD.');
      }
    },

    {
      id: 'pipeline_with_misses',
      tier: 3,
      tags: ['pipelining', 'misses', 'preconditions'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 4);
        var rowOld = rrow(rng, topo);
        var rowNew = rrow_avoid(rng, topo, rowOld);
        var rows = [rrow(rng, topo), rowNew, rrow(rng, topo), rrow(rng, topo)];
        var reqs = banks.map(function (bank, i) {
          return DDRD.make_req('RD', bank, rows[i], rcol(rng, topo));
        });
        return scenario(reqs,
          open_state(topo, [{ bank: banks[1], row: rowOld }]),
          'open',
          'ACT pipelining needs three things at once: same direction, ' +
          'distinct banks, and ZERO page misses. Four reads to four ' +
          'banks nearly qualify -- but B' + banks[1] + ' has R' + rowOld +
          ' open and wants R' + rowNew + ', so the whole schedule falls ' +
          'back to in-order: each ACT sits with its own column command ' +
          'and the conflict pays PRE + ACT inline. One miss kills the ' +
          'pipeline for everyone.');
      }
    },

    {
      id: 'full_mix_hard',
      tier: 3,
      tags: ['capstone', 'turnaround', 'misses'],
      requires: {},
      generate: function (topo, rng) {
        var banks = pick_banks(rng, topo, 4);
        var rowHit0 = rrow(rng, topo);
        var rowHit1 = rrow(rng, topo);
        var rowOld = rrow(rng, topo);
        var rowNew = rrow_avoid(rng, topo, rowOld);
        var rowIdle = rrow(rng, topo);
        var reqs = [
          DDRD.make_req('WR', banks[0], rowHit0, rcol(rng, topo)),
          DDRD.make_req('RD', banks[1], rowHit1, rcol(rng, topo)),
          DDRD.make_req('RD', banks[2], rowNew, rcol(rng, topo)),
          DDRD.make_req('WR', banks[3], rowIdle, rcol(rng, topo)),
          DDRD.make_req('RD', banks[0], rowHit0, rcol(rng, topo))
        ];
        var explanation;
        if (topo.hasBankGroups) {
          var gw = DDRD.bg(topo, banks[0]);
          var gr = DDRD.bg(topo, banks[1]);
          explanation =
            'Everything at once. The opening write is a page hit in ' +
            'group ' + gw + '; the read behind it is a hit in group ' +
            gr + ' -- a write-to-read direction change, so the (tWTR ' +
            'bubble) appears even though the cross-group pair uses the ' +
            'short tWTRS internally. The third request is a row conflict ' +
            '(PRE + ACT inline; one miss kills any pipelining), the ' +
            'fourth flips the bus back to write (tRTW bubble) on an idle ' +
            'bank, and the last read turns it again. Three direction ' +
            'changes in five requests: this is where bandwidth goes to ' +
            'die.';
        } else {
          explanation =
            'Everything at once. The opening write is a page hit; the ' +
            'read behind it forces a write-to-read direction change ' +
            '(tWTR bubble). The third request is a row conflict -- PRE ' +
            '+ ACT inline, and one miss kills any pipelining -- the ' +
            'fourth flips the bus back to write (tRTW bubble) on an ' +
            'idle bank, and the last read turns it again. With no bank ' +
            'groups there is no tWTRS/tWTRL distinction: every ' +
            'write-to-read pays the same tWTR. Three direction changes ' +
            'in five requests: this is where bandwidth goes to die.';
        }
        return scenario(reqs,
          open_state(topo, [{ bank: banks[0], row: rowHit0 },
                            { bank: banks[1], row: rowHit1 },
                            { bank: banks[2], row: rowOld }]),
          'open', explanation);
      }
    }
  ];

  // -- filter / build API ----------------------------------------------------

  function meets_requires(gen, topo) {
    var r = gen.requires || {};
    if (r.bankGroups && !topo.hasBankGroups) {
      return false;
    }
    if (r.sids && (topo.sids || 0) < r.sids) {
      return false;
    }
    return true;
  }

  // Generators whose requires the topology satisfies.
  function availableGenerators(topo) {
    return generators.filter(function (g) {
      return meets_requires(g, topo);
    });
  }

  function getGenerator(id) {
    for (var i = 0; i < generators.length; i++) {
      if (generators[i].id === id) {
        return generators[i];
      }
    }
    return null;
  }

  // buildScenario(genOrId, topo, policyDefault, rng) -> Scenario:
  //   {id, tier, tags, reqs, bankState, policy, explanation,
  //    correct: {cmds, reasons}, reordered (frfcfs only, else null),
  //    options: [{cmds, reasons?, correct} x4]}  -- index 0 is correct;
  //    the UI shuffles, this layer never does.
  function buildScenario(genOrId, topo, policyDefault, rng) {
    var gen = typeof genOrId === 'string' ? getGenerator(genOrId) : genOrId;
    if (!gen) {
      throw new Error('unknown scenario generator: ' + genOrId);
    }
    var produced = gen.generate(topo, rng);
    var policy = produced.policy || policyDefault || 'open';
    var opts = produced.opts || null;
    var correct = DDRD.schedule_with_policy(policy, produced.reqs,
                                            produced.bankState, topo, opts);
    var ctx = {
      reqs: produced.reqs,
      bankState: produced.bankState,
      topo: topo,
      opts: opts,
      policy: policy,
      rng: rng
    };
    var wrongs = DDRD.make_wrong_answers(correct.cmds, ctx);
    var options = [{
      cmds: correct.cmds,
      reasons: correct.reasons,
      correct: true
    }].concat(wrongs.map(function (w) {
      return { cmds: w, correct: false };
    }));
    return {
      id: gen.id,
      tier: gen.tier,
      tags: gen.tags,
      reqs: produced.reqs,
      bankState: produced.bankState,
      policy: policy,
      explanation: produced.explanation,
      correct: { cmds: correct.cmds, reasons: correct.reasons },
      reordered: correct.reordered || null,
      options: options
    };
  }

  DDRD.scenario_generators = generators;
  DDRD.availableGenerators = availableGenerators;
  DDRD.getGenerator = getGenerator;
  DDRD.buildScenario = buildScenario;
})(DDRD);
