// test_mutate.js -- mutator behavior and the make_wrong_answers invariants:
// exactly 3 wrongs, textually distinct from correct and each other, and
// every wrong differs from correct in its REAL-command subsequence
// (annotations never count as a difference).
var SUITES = (typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES ||
             ((typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES = []);

(function () {
  'use strict';

  var DDRD = globalThis.DDRD;

  function topoBG() {
    return { hasBankGroups: true, groups: 2, banksPerGroup: 4,
             banks: 8, rows: 8, cols: 8, sids: 2 };
  }

  function req(op, b, r, c) {
    return DDRD.make_req(op, b, r, c);
  }

  function fmt(cmds) {
    return DDRD.format_schedule(cmds);
  }

  function realFmt(cmds) {
    return DDRD.format_real(cmds);
  }

  function mutatorByName(name) {
    var i = DDRD.mutator_names.indexOf(name);
    return DDRD.mutators[i];
  }

  SUITES.push({
    name: 'mutate',
    run: function (t) {
      var topo = topoBG();

      // -- catalog order ----------------------------------------------------
      t.deepEq(DDRD.mutator_names,
               ['skip_pre', 'add_unnecessary_act', 'skip_act',
                'skip_turnaround', 'serialize_acts', 'reverse_rd_order',
                'wrong_policy'],
               'mutator catalog has the 7 documented mutators in order');

      // -- individual mutator behavior ---------------------------------------
      var missState = DDRD.make_bank_state(topo);
      missState[3].openRow = 2;
      var missSched = DDRD.schedule_open_page(
        [req('RD', 3, 5, 2), req('RD', 3, 5, 7)], missState, topo, null);
      var ctxMiss = { reqs: [req('RD', 3, 5, 2), req('RD', 3, 5, 7)],
                      bankState: missState, topo: topo, policy: 'open' };
      // missSched: PRE B3 / ACT B3 R5 / RD B3 C2 / RD B3 C7

      t.eq(fmt(mutatorByName('skip_pre')(missSched.cmds, ctxMiss)),
           'ACT B3 R5\nRD B3 C2\nRD B3 C7',
           'skip_pre drops the first PRE');
      t.eq(mutatorByName('skip_pre')(
             DDRD.schedule_open_page([req('RD', 3, 5, 2)],
                                     (function () {
                                       var s = DDRD.make_bank_state(topo);
                                       s[3].openRow = 5;
                                       return s;
                                     })(), topo, null).cmds, ctxMiss),
           null, 'skip_pre is null without a PRE');

      t.eq(fmt(mutatorByName('skip_act')(missSched.cmds, ctxMiss)),
           'PRE B3\nRD B3 C2\nRD B3 C7',
           'skip_act drops the first ACT');

      t.eq(fmt(mutatorByName('add_unnecessary_act')(missSched.cmds, ctxMiss)),
           'PRE B3\nACT B3 R5\nACT B3 R5\nRD B3 C2\nRD B3 C7',
           'add_unnecessary_act re-activates an already-open row');

      // skip_turnaround: removes an annotation, null without one.
      var hitState = DDRD.make_bank_state(topo);
      hitState[1].openRow = 2;
      hitState[4].openRow = 6;
      var turnReqs = [req('WR', 1, 2, 0), req('RD', 4, 6, 1)];
      var turnSched = DDRD.schedule_open_page(turnReqs, hitState, topo, null);
      var ctxTurn = { reqs: turnReqs, bankState: hitState, topo: topo,
                      policy: 'open' };
      t.eq(fmt(mutatorByName('skip_turnaround')(turnSched.cmds, ctxTurn)),
           'WR B1 C0\nRD B4 C1',
           'skip_turnaround drops the bubble annotation');
      t.eq(mutatorByName('skip_turnaround')(missSched.cmds, ctxMiss), null,
           'skip_turnaround is null without annotations');

      // serialize_acts on a pipelined schedule.
      var pipeReqs = [req('RD', 0, 1, 1), req('RD', 2, 3, 2),
                      req('RD', 5, 0, 3)];
      var pipeSched = DDRD.schedule_open_page(
        pipeReqs, DDRD.make_bank_state(topo), topo, null);
      var ctxPipe = { reqs: pipeReqs, bankState: DDRD.make_bank_state(topo),
                      topo: topo, policy: 'open' };
      t.eq(fmt(mutatorByName('serialize_acts')(pipeSched.cmds, ctxPipe)),
           'ACT B0 R1\nRD B0 C1\nACT B2 R3\nRD B2 C2\nACT B5 R0\nRD B5 C3',
           'serialize_acts interleaves ACT/column pairs');
      t.eq(mutatorByName('serialize_acts')(missSched.cmds, ctxMiss), null,
           'serialize_acts is null without a phase-1 ACT run');

      // reverse_rd_order on a hit stream.
      var hitReqs = [req('RD', 2, 5, 1), req('RD', 2, 5, 3),
                     req('RD', 2, 5, 6)];
      var hitOnly = DDRD.schedule_open_page(
        hitReqs, (function () {
          var s = DDRD.make_bank_state(topo);
          s[2].openRow = 5;
          return s;
        })(), topo, null);
      var ctxHit = { reqs: hitReqs, bankState: hitOnly.bankState, topo: topo,
                     policy: 'open' };
      t.eq(fmt(mutatorByName('reverse_rd_order')(hitOnly.cmds, ctxHit)),
           'RD B2 C6\nRD B2 C3\nRD B2 C1',
           'reverse_rd_order reverses the read run');
      t.eq(mutatorByName('reverse_rd_order')(
             DDRD.schedule_open_page([req('RD', 2, 5, 1)],
                                     (function () {
                                       var s = DDRD.make_bank_state(topo);
                                       s[2].openRow = 5;
                                       return s;
                                     })(), topo, null).cmds, ctxHit),
           null, 'reverse_rd_order is null on a single read');

      // wrong_policy flips open <-> close.
      var closed = mutatorByName('wrong_policy')(hitOnly.cmds, ctxHit);
      t.ok(fmt(closed).indexOf('RDA B2 C1') !== -1,
           'wrong_policy re-runs close-page on an open-page schedule');
      var ctxClose = { reqs: hitReqs, bankState: ctxHit.bankState, topo: topo,
                       policy: 'close' };
      var closeSched = DDRD.schedule_close_page(hitReqs, ctxHit.bankState,
                                                topo);
      var opened = mutatorByName('wrong_policy')(closeSched.cmds, ctxClose);
      t.ok(fmt(opened).indexOf('RD B2 C1') !== -1 &&
           fmt(opened).indexOf('RDA') === -1,
           'wrong_policy re-runs open-page on a close-page schedule');

      // mutators never mutate their input array.
      var frozenInput = pipeSched.cmds.slice();
      var snapshot = fmt(frozenInput);
      DDRD.mutators.forEach(function (m) {
        m(frozenInput, ctxPipe);
      });
      t.eq(fmt(frozenInput), snapshot,
           'no mutator mutates its input cmds array');

      // -- make_wrong_answers invariants --------------------------------------

      // A matrix of representative correct schedules with their ctx.
      function cases() {
        var s1 = DDRD.make_bank_state(topo);
        s1[2].openRow = 5;
        var s2 = DDRD.make_bank_state(topo);
        s2[1].openRow = 2;
        s2[4].openRow = 6;
        var s3 = DDRD.make_bank_state(topo);
        s3[3].openRow = 2;
        var s4 = DDRD.make_bank_state(topo);
        s4[3].openRow = 5;
        return [
          { // all-hit stream
            reqs: hitReqs, bankState: s1, policy: 'open'
          },
          { // turnaround schedule (WR then RD hits)
            reqs: turnReqs, bankState: s2, policy: 'open'
          },
          { // miss then hits
            reqs: [req('RD', 3, 5, 2), req('RD', 3, 5, 7),
                   req('RD', 6, 1, 0)],
            bankState: (function () {
              var s = DDRD.make_bank_state(topo);
              s[3].openRow = 2;
              s[6].openRow = 1;
              return s;
            })(), policy: 'open'
          },
          { // pipelined
            reqs: pipeReqs, bankState: DDRD.make_bank_state(topo),
            policy: 'open'
          },
          { // close-page policy
            reqs: [req('RD', 3, 2, 1), req('WR', 5, 6, 0),
                   req('RD', 3, 2, 7)],
            bankState: DDRD.make_bank_state(topo), policy: 'close'
          },
          { // frfcfs policy
            reqs: [req('RD', 3, 2, 0), req('RD', 1, 4, 0),
                   req('RD', 3, 5, 7)],
            bankState: s4, policy: 'frfcfs'
          }
        ];
      }

      for (var seed = 0; seed < 30; seed++) {
        cases().forEach(function (cs, ci) {
          var correct = DDRD.schedule_with_policy(
            cs.policy, cs.reqs, cs.bankState, topo, null);
          var ctx = { reqs: cs.reqs, bankState: cs.bankState, topo: topo,
                      policy: cs.policy,
                      rng: DDRD.mulberry32(seed * 100 + ci) };
          var wrongs = DDRD.make_wrong_answers(correct.cmds, ctx);
          t.eq(wrongs.length, 3,
               'case ' + ci + ' seed ' + seed + ': exactly 3 wrong answers');

          var texts = {};
          wrongs.forEach(function (w, wi) {
            var text = fmt(w);
            t.ok(text !== fmt(correct.cmds),
                 'case ' + ci + ' seed ' + seed + ' wrong ' + wi +
                 ': text differs from correct');
            t.ok(!texts[text],
                 'case ' + ci + ' seed ' + seed + ' wrong ' + wi +
                 ': text unique among wrongs');
            texts[text] = true;
            t.ok(realFmt(w) !== realFmt(correct.cmds),
                 'case ' + ci + ' seed ' + seed + ' wrong ' + wi +
                 ': real-command subsequence differs from correct');
          });

          // The skip_turnaround-only wrong must never appear: no wrong may
          // be the correct schedule with annotations stripped.
          wrongs.forEach(function (w) {
            t.ok(!(DDRD.format_real(w) === realFmt(correct.cmds)),
                 'case ' + ci + ' seed ' + seed +
                 ': no annotation-only difference survives');
          });
        });
      }

      // -- fallbacks ----------------------------------------------------------
      t.eq(fmt(DDRD.swap_adjacent(hitOnly.cmds)),
           'RD B2 C3\nRD B2 C1\nRD B2 C6',
           'swap_adjacent swaps the first adjacent column pair');
      t.eq(DDRD.swap_adjacent(
             DDRD.schedule_open_page([req('RD', 2, 5, 1)],
                                     (function () {
                                       var s = DDRD.make_bank_state(topo);
                                       s[2].openRow = 5;
                                       return s;
                                     })(), topo, null).cmds),
           null, 'swap_adjacent is null with fewer than two columns');
      t.eq(fmt(DDRD.drop_cmd(hitOnly.cmds)), 'RD B2 C3\nRD B2 C6',
           'drop_cmd drops the first column command');

      // Degenerate one-command schedule: mutators plus drop_cmd must still
      // reach exactly 3 without throwing.
      var tinyState = DDRD.make_bank_state(topo);
      tinyState[1].openRow = 2;
      var tinyCorrect = DDRD.schedule_open_page(
        [req('WR', 1, 2, 0)], tinyState, topo, null);
      var tinyWrongs = DDRD.make_wrong_answers(tinyCorrect.cmds, {
        reqs: [req('WR', 1, 2, 0)], bankState: tinyState, topo: topo,
        policy: 'open', rng: DDRD.mulberry32(7)
      });
      t.eq(tinyWrongs.length, 3,
           'degenerate single-command schedule still yields 3 wrongs');
      t.deepEq(tinyWrongs.map(realFmt).sort(),
               ['', 'ACT B1 R2\nWR B1 C0', 'PRE B1\nACT B1 R2\nWRA B1 C0'],
               'fallback drop_cmd participates when mutators exhaust');
    }
  });
})();
