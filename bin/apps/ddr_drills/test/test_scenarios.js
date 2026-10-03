// test_scenarios.js -- the 19 generators: catalog shape, topology bounds,
// requires filtering, degradation explanations, buildScenario shape, and
// the make_wrong_answers never-throws sweep across generators x topologies
// x seeds.
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

  var EXPECTED_IDS = [
    'empty_page_sequential', 'page_hit_stream', 'single_page_miss',
    'close_page_basics',
    'cross_group_streams', 'act_pipelining', 'twtr_turnaround',
    'trtw_turnaround', 'mixed_open_close_compare', 'interleave_banks',
    'tfaw_window', 'sid_pair_streams', 'hit_miss_mix',
    'frfcfs_basic', 'frfcfs_vs_fcfs_compare', 'tccdr_sid_spacing',
    'cross_group_turnaround', 'pipeline_with_misses', 'full_mix_hard'
  ];

  var BG_SID_ONLY = ['cross_group_streams', 'sid_pair_streams',
                     'tccdr_sid_spacing', 'cross_group_turnaround'];

  SUITES.push({
    name: 'scenarios',
    run: function (t) {
      var gens = DDRD.scenario_generators;
      var bg = topoBG();
      var flat = topoFlat();

      // -- catalog shape ------------------------------------------------------
      t.eq(gens.length, 19, 'exactly 19 scenario generators');
      t.deepEq(gens.map(function (g) { return g.id; }), EXPECTED_IDS,
               'generator ids in catalog order');
      var tiers = { 1: 0, 2: 0, 3: 0 };
      gens.forEach(function (g) {
        tiers[g.tier]++;
        t.ok(Array.isArray(g.tags) && g.tags.length > 0,
             g.id + ': has tags');
        t.ok(g.requires && typeof g.requires === 'object',
             g.id + ': has a requires object');
      });
      t.deepEq([tiers[1], tiers[2], tiers[3]], [4, 9, 6],
               'tier counts are 4 / 9 / 6');

      // -- requires filtering ---------------------------------------------------
      var availBG = DDRD.availableGenerators(bg).map(function (g) {
        return g.id;
      });
      t.eq(availBG.length, 19, 'BG+SID topology offers all 19 generators');
      var availFlat = DDRD.availableGenerators(flat).map(function (g) {
        return g.id;
      });
      t.eq(availFlat.length, 15,
           'flat topology excludes the 4 BG/SID-only generators');
      t.deepEq(BG_SID_ONLY.filter(function (id) {
        return availFlat.indexOf(id) !== -1;
      }), [], 'flat topology excludes exactly the BG/SID-only ids');
      t.deepEq(EXPECTED_IDS.filter(function (id) {
        return BG_SID_ONLY.indexOf(id) === -1 &&
               availFlat.indexOf(id) === -1;
      }), [], 'flat topology keeps every other generator');

      // -- topology-bounded addresses + never-throws sweep ----------------------
      [['BG', bg], ['flat', flat]].forEach(function (pair) {
        var label = pair[0];
        var topo = pair[1];
        DDRD.availableGenerators(topo).forEach(function (gen) {
          for (var seed = 0; seed < 20; seed++) {
            var rng = DDRD.mulberry32(seed * 7919 + 13);
            var sc;
            var threw = false;
            try {
              sc = DDRD.buildScenario(gen, topo, 'open', rng);
            } catch (e) {
              threw = true;
            }
            t.ok(!threw,
                 label + ' ' + gen.id + ' seed ' + seed +
                 ': buildScenario never throws');
            if (threw) {
              continue;
            }

            // Address bounds on every request.
            sc.reqs.forEach(function (r, ri) {
              var inBounds =
                (r.op === 'RD' || r.op === 'WR') &&
                r.bank >= 0 && r.bank < topo.banks &&
                r.row >= 0 && r.row < topo.rows &&
                r.col >= 0 && r.col < topo.cols &&
                (r.sid === undefined ||
                 (topo.sids > 0 && r.sid >= 0 && r.sid < topo.sids));
              t.ok(inBounds,
                   label + ' ' + gen.id + ' seed ' + seed + ' req ' + ri +
                   ': address within topology bounds');
            });
            // Bank state shape and bounds.
            t.eq(sc.bankState.length, topo.banks,
                 label + ' ' + gen.id + ' seed ' + seed +
                 ': bank state length == topo.banks');
            t.ok(sc.bankState.every(function (e) {
              return e.openRow === null ||
                     (e.openRow >= 0 && e.openRow < topo.rows);
            }), label + ' ' + gen.id + ' seed ' + seed +
               ': open rows within bounds');

            // Scenario shape: 4 options, exactly one correct at index 0.
            t.eq(sc.options.length, 4,
                 label + ' ' + gen.id + ' seed ' + seed + ': 4 options');
            t.ok(sc.options[0].correct === true &&
                 sc.options.slice(1).every(function (o) {
                   return o.correct === false;
                 }),
                 label + ' ' + gen.id + ' seed ' + seed +
                 ': option 0 is the sole correct answer (unshuffled)');
            var texts = sc.options.map(function (o) {
              return DDRD.format_schedule(o.cmds);
            });
            var unique = {};
            var allUnique = true;
            texts.forEach(function (x) {
              if (unique[x]) {
                allUnique = false;
              }
              unique[x] = true;
            });
            t.ok(allUnique,
                 label + ' ' + gen.id + ' seed ' + seed +
                 ': all 4 options textually distinct');
            t.ok(typeof sc.explanation === 'string' &&
                 sc.explanation.length > 0 &&
                 /^[\x00-\x7F]*$/.test(sc.explanation),
                 label + ' ' + gen.id + ' seed ' + seed +
                 ': non-empty ASCII explanation');
            t.ok(['open', 'close', 'frfcfs'].indexOf(sc.policy) !== -1,
                 label + ' ' + gen.id + ' seed ' + seed +
                 ': declared policy is a known policy');

            // Determinism: same seed -> identical scenario.
            var again = DDRD.buildScenario(
              gen, topo, 'open', DDRD.mulberry32(seed * 7919 + 13));
            t.eq(DDRD.format_schedule(again.options[0].cmds), texts[0],
                 label + ' ' + gen.id + ' seed ' + seed +
                 ': deterministic for a fixed seed');
          }
        });
      });

      // -- degradation explanations differ by topology --------------------------
      ['act_pipelining', 'full_mix_hard'].forEach(function (id) {
        for (var seed = 0; seed < 5; seed++) {
          var onBG = DDRD.buildScenario(id, bg, 'open',
                                        DDRD.mulberry32(seed));
          var onFlat = DDRD.buildScenario(id, flat, 'open',
                                          DDRD.mulberry32(seed));
          t.ok(onBG.explanation !== onFlat.explanation,
               id + ' seed ' + seed +
               ': BG-keyed explanation variant differs by topology');
        }
      });

      // -- frfcfs scenarios expose the reordered queue ---------------------------
      var fr = DDRD.buildScenario('frfcfs_basic', bg, 'open',
                                  DDRD.mulberry32(42));
      t.ok(Array.isArray(fr.reordered) &&
           fr.reordered.length === fr.reqs.length,
           'frfcfs scenario returns the reordered request list');
      t.eq(fr.policy, 'frfcfs', 'frfcfs scenario declares its policy');
      var plain = DDRD.buildScenario('page_hit_stream', bg, 'open',
                                     DDRD.mulberry32(42));
      t.eq(plain.reordered, null,
           'non-frfcfs scenario has no reordered list');
    }
  });
})();
