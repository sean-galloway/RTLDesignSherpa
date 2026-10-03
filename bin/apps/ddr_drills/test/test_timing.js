// test_timing.js -- timing-drill matcher: scope computation, pattern
// alternation/wildcards, the diff_bank subsumption rule, annotation
// skipping, golden matchParams pairs on the HBM4 pack, and the
// buildTimingQuestion window/answer contract.
var SUITES = (typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES ||
             ((typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES = []);

(function () {
  'use strict';

  var DDRD = globalThis.DDRD;

  var BG = { hasBankGroups: true, groups: 2, banksPerGroup: 4,
             banks: 8, rows: 8, cols: 8, sids: 2 };
  var FLAT = { hasBankGroups: false, groups: 1, banksPerGroup: 8,
               banks: 8, rows: 8, cols: 8, sids: 0 };

  function cmd(type, bank, sid) {
    var c = { type: type, bank: bank };
    if (sid !== undefined) { c.sid = sid; }
    return c;
  }

  SUITES.push({
    name: 'timing',
    run: function (T) {
      var pack = DDRD.getPack('hbm4');
      T.ok(!!pack, 'hbm4 pack registered');

      // -- computeScope --------------------------------------------------
      T.eq(DDRD.computeScope(BG, cmd('RD', 0), cmd('RD', 0)),
           'same_bank', 'scope: same bank on BG topo');
      T.eq(DDRD.computeScope(BG, cmd('RD', 0), cmd('RD', 3)),
           'same_group', 'scope: same group on BG topo');
      T.eq(DDRD.computeScope(BG, cmd('RD', 0), cmd('RD', 4)),
           'diff_group', 'scope: different groups on BG topo');
      T.eq(DDRD.computeScope(FLAT, cmd('RD', 0), cmd('RD', 0)),
           'same_bank', 'scope: same bank on flat topo');
      T.eq(DDRD.computeScope(FLAT, cmd('RD', 0), cmd('RD', 5)),
           'diff_bank', 'scope: different banks on flat topo');
      T.eq(DDRD.computeScope(BG, cmd('RD', 0, 0), cmd('RD', 0, 1)),
           'diff_sid', 'scope: same bank number, different SIDs');
      T.eq(DDRD.computeScope(BG, cmd('RD', 0, 0), cmd('RD', 4, 1)),
           'diff_sid', 'scope: SID wins over group comparison');
      T.eq(DDRD.computeScope(FLAT, cmd('RD', 0), cmd('RD', 0)),
           'same_bank', 'scope: no sid fields on flat topo');

      // -- patternMatch ---------------------------------------------------
      T.ok(DDRD.patternMatch('RD|RDA', 'RD'), 'pattern: alternation hit');
      T.ok(DDRD.patternMatch('RD|RDA', 'RDA'), 'pattern: alternation tail');
      T.ok(!DDRD.patternMatch('RD|RDA', 'WR'), 'pattern: alternation miss');
      T.ok(DDRD.patternMatch('*', 'PRE'), 'pattern: wildcard');
      T.ok(DDRD.patternMatch('ACT', 'ACT'), 'pattern: exact');

      // -- golden matchParams pairs (HBM4 pack, in pack order) ------------
      function gold(a, b, expected, label) {
        T.deepEq(DDRD.matchParams(pack, BG, a, b), expected, label);
      }

      gold(cmd('ACT', 0), cmd('RD', 0), ['tRCDRD'], 'ACT->RD same bank');
      gold(cmd('ACT', 0), cmd('WR', 0), ['tRCDWR'], 'ACT->WR same bank');
      gold(cmd('ACT', 0), cmd('RDA', 0), ['tRCDRD'],
           'ACT->RDA matches via alternation');
      gold(cmd('ACT', 0), cmd('PRE', 0), ['tRAS'], 'ACT->PRE same bank');
      gold(cmd('PRE', 0), cmd('ACT', 0), ['tRP'], 'PRE->ACT same bank');
      gold(cmd('ACT', 0), cmd('ACT', 0), ['tRC', 'tFAW'],
           'ACT->ACT same bank: tRC plus tFAW (any scope)');
      gold(cmd('ACT', 0), cmd('ACT', 1), ['tRRDL', 'tFAW'],
           'ACT->ACT same group');
      gold(cmd('ACT', 0), cmd('ACT', 4), ['tRRDS', 'tFAW'],
           'ACT->ACT across groups');
      gold(cmd('RD', 0), cmd('PRE', 0), ['tRTP'], 'RD->PRE same bank');
      gold(cmd('WRA', 0), cmd('PRE', 0), ['tWR'], 'WRA->PRE same bank');
      gold(cmd('PRE', 0), cmd('PRE', 5), ['tPPD'], 'PRE->PRE anywhere');
      gold(cmd('RD', 0), cmd('RD', 1), ['tCCDL'], 'RD->RD same group');
      gold(cmd('WR', 1), cmd('WRA', 2), ['tCCDL'], 'WR->WRA same group');
      gold(cmd('RD', 0), cmd('RD', 4), ['tCCDS'], 'RD->RD across groups');
      gold(cmd('RD', 0, 0), cmd('RD', 0, 1), ['tCCDR'],
           'RD->RD across SIDs: tCCDR, NOT tCCDS');
      gold(cmd('RD', 0, 0), cmd('RDA', 5, 1), ['tCCDR'],
           'RD->RDA across SIDs');
      // Direction changes match BOTH the column-spacing param (tCCDL/tCCDS
      // patterns cover all four column types on both sides) AND the
      // turnaround param - both genuinely constrain the gap.
      gold(cmd('WR', 0), cmd('RD', 0), ['tCCDL', 'tWTRL'], 'WR->RD same bank');
      gold(cmd('WR', 0), cmd('RD', 3), ['tCCDL', 'tWTRL'], 'WR->RD same group');
      gold(cmd('WR', 0), cmd('RD', 4), ['tCCDS', 'tWTRS'], 'WR->RD across groups');
      gold(cmd('RD', 0), cmd('WR', 7), ['tCCDS', 'tRTW'], 'RD->WR anywhere');
      gold(cmd('RDA', 2), cmd('WRA', 2), ['tCCDL', 'tRTW'], 'RDA->WRA same bank');
      gold(cmd('PRE', 0), cmd('ACT', 1), [],
           'PRE->ACT different banks: nothing governs');
      gold(cmd('RD', 0), cmd('ACT', 0), [], 'RD->ACT: no rule');
      gold(cmd('WR', 0, 0), cmd('WR', 0, 1), [],
           'WR->WR across SIDs: no diff_sid write rule, tCCDS does NOT ' +
           'fire (documented: diff_sid pairs match only diff_sid/any rules)');

      // Annotations never match, even with real command types nearby.
      T.deepEq(DDRD.matchParams(pack, BG,
                                DDRD.make_annotation('(tWTR bubble)', 'x'),
                                cmd('RD', 0)),
               [], 'matchParams: annotation input yields empty');

      // -- diff_bank one-way subsumption ----------------------------------
      var fakePack = {
        topology: BG,
        timingParams: [
          { symbol: 'tX', name: 'fake', chapter: 'core',
            definition: 'fake rule for subsumption testing',
            appliesTo: [{ from: 'RD', to: 'RD', scope: 'diff_bank' }] }
        ]
      };
      T.deepEq(DDRD.matchParams(fakePack, BG, cmd('RD', 0), cmd('RD', 4)),
               ['tX'], 'subsumption: diff_bank rule fires on diff_group');
      T.deepEq(DDRD.matchParams(fakePack, BG, cmd('RD', 0, 0), cmd('RD', 2, 1)),
               ['tX'], 'subsumption: diff_bank rule fires on diff_sid');
      T.deepEq(DDRD.matchParams(fakePack, BG, cmd('RD', 0), cmd('RD', 1)),
               [], 'subsumption: diff_bank rule does NOT fire on same_group');
      T.deepEq(DDRD.matchParams(fakePack, FLAT, cmd('RD', 0), cmd('RD', 2)),
               ['tX'], 'diff_bank rule fires natively on flat topo');

      // -- timingCandidatePairs: annotations skipped ----------------------
      var sched = [
        DDRD.make_cmd('ACT', 0, 3),
        DDRD.make_cmd('WR', 0, null, 1),
        DDRD.make_annotation('(tWTR bubble)', 'WR->RD turnaround'),
        DDRD.make_cmd('RD', 0, null, 2),
        DDRD.make_cmd('PRE', 0)
      ];
      var pairs = DDRD.timingCandidatePairs(pack, BG, sched);
      T.deepEq(pairs, [{ prevIdx: 0, nextIdx: 1 },
                       { prevIdx: 1, nextIdx: 3 },
                       { prevIdx: 3, nextIdx: 4 }],
               'candidate pairs span the annotation (WR->RD askable)');

      // A schedule whose only real pair has no governing param yields none.
      var dry = [DDRD.make_cmd('PRE', 0), DDRD.make_cmd('ACT', 1)];
      T.deepEq(DDRD.timingCandidatePairs(pack, BG, dry), [],
               'candidate pairs: ungoverned gaps excluded');

      // -- buildTimingQuestion --------------------------------------------
      for (var seed = 1; seed <= 30; seed++) {
        var q = DDRD.buildTimingQuestion(pack, DDRD.mulberry32(seed));
        T.ok(q.answer.length > 0,
             'seed ' + seed + ': answer non-empty (' + q.genId + ')');
        T.ok(q.gapAfter + 1 < q.window.length,
             'seed ' + seed + ': gap fits inside window');
        var annotated = q.window.some(function (c) { return c.annotation; });
        T.ok(!annotated, 'seed ' + seed + ': window has no annotations');
        T.deepEq(DDRD.matchParams(pack, BG, q.window[q.gapAfter],
                                  q.window[q.gapAfter + 1]),
                 q.answer,
                 'seed ' + seed + ': answer equals matcher on window gap');
        q.answer.forEach(function (s) {
          T.ok(q.allSymbols.indexOf(s) !== -1,
               'seed ' + seed + ': answer symbol ' + s + ' is a pack param');
        });
      }

      var q1 = DDRD.buildTimingQuestion(pack, DDRD.mulberry32(42));
      var q2 = DDRD.buildTimingQuestion(pack, DDRD.mulberry32(42));
      T.eq(q1.genId, q2.genId, 'deterministic: same seed, same generator');
      T.deepEq(q1.answer, q2.answer,
               'deterministic: same seed, same answer');

      // The question builder works against EVERY registered pack (flat
      // topologies included - fewer generators, fewer scopes, same
      // contract).
      DDRD.listPacks().forEach(function (p) {
        for (var s = 1; s <= 10; s++) {
          var qp = DDRD.buildTimingQuestion(p, DDRD.mulberry32(s * 7));
          T.ok(qp.answer.length > 0,
               'pack ' + p.id + ' seed ' + s + ': answer non-empty');
          T.deepEq(DDRD.matchParams(p, p.topology, qp.window[qp.gapAfter],
                                    qp.window[qp.gapAfter + 1]),
                   qp.answer,
                   'pack ' + p.id + ' seed ' + s + ': answer matches gap');
        }
      });
    }
  });
})();
