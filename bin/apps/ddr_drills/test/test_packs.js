// test_packs.js -- pack schema and content-shape validation for every
// registered pack. Registers its suite on globalThis.DDRD_TEST_SUITES;
// run_tests.js supplies the assertion kit.
var SUITES = (typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES ||
             ((typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES = []);

(function () {
  'use strict';

  var DDRD = globalThis.DDRD;

  var KNOWN_SCOPES = ['same_bank', 'same_group', 'diff_group', 'diff_bank',
                      'diff_sid', 'any'];

  SUITES.push({
    name: 'packs',
    run: function (T) {
      var packs = DDRD.listPacks();
      T.ok(packs.length >= 1, 'at least one pack registered');

      packs.forEach(function (pack) {
        var tag = 'pack ' + pack.id + ': ';

        var v = DDRD.validatePack(pack);
        T.ok(v.ok, tag + 'validatePack ok' +
             (v.ok ? '' : ' -- ' + v.errors.join('; ')));

        // Topology sanity and engine compatibility.
        T.ok(pack.topology.banks === 8 && pack.topology.rows === 8 &&
             pack.topology.cols === 8,
             tag + 'uses the simplified 8-bank/8-row/8-col drill model');
        var engineCmds = ['ACT', 'PRE', 'RD', 'WR', 'RDA', 'WRA'];
        engineCmds.forEach(function (c) {
          T.ok(pack.commands.indexOf(c) !== -1,
               tag + 'commands include ' + c);
        });

        // Question bank: shape, uniqueness, correct-first convention,
        // content floor, chapters present.
        T.ok(pack.questionBank.length >= 8,
             tag + 'question bank has >= 8 questions (' +
             pack.questionBank.length + ')');
        var chapters = {};
        pack.questionBank.forEach(function (q, i) {
          var qt = tag + 'q[' + i + ']: ';
          T.ok(q.answers.length >= 2, qt + '>= 2 answers');
          var seen = {};
          var dup = false;
          q.answers.forEach(function (a) {
            if (seen[a]) { dup = true; }
            seen[a] = true;
          });
          T.ok(!dup, qt + 'answers are distinct');
          T.ok(q.answers[0].length > 0, qt + 'answers[0] (correct) non-empty');
          T.ok(typeof q.chapter === 'string' && q.chapter.length > 0,
               qt + 'has a chapter tag');
          T.ok(typeof q.source === 'string' && q.source.length > 0,
               qt + 'cites a source');
          chapters[q.chapter] = true;
        });
        T.ok(Object.keys(chapters).length >= 3,
             tag + 'questions span >= 3 chapters (' +
             Object.keys(chapters).join(',') + ')');

        // Timing params: shape, known scopes, engine-reachable params
        // only reference engine commands; reference-panel-only params
        // (refresh) may use REF.
        T.ok(pack.timingParams.length >= 10,
             tag + 'timing table has >= 10 params (' +
             pack.timingParams.length + ')');
        var symbols = {};
        pack.timingParams.forEach(function (p, i) {
          var pt = tag + 'timing[' + p.symbol + ']: ';
          T.ok(!symbols[p.symbol], pt + 'symbol unique');
          symbols[p.symbol] = true;
          T.ok(typeof p.definition === 'string' && p.definition.length > 10,
               pt + 'has a real definition');
          p.appliesTo.forEach(function (rule, j) {
            T.ok(KNOWN_SCOPES.indexOf(rule.scope) !== -1,
                 pt + 'appliesTo[' + j + '] scope "' + rule.scope +
                 '" is known');
          });
        });

        // Command reference: one doc entry per engine command, each with
        // a name and a real description (the Commands tab renders these).
        T.ok(Array.isArray(pack.commandDocs) && pack.commandDocs.length >= 6,
             tag + 'commandDocs has >= 6 entries (' +
             (pack.commandDocs ? pack.commandDocs.length : 0) + ')');
        var documented = {};
        (pack.commandDocs || []).forEach(function (c, i) {
          var ct = tag + 'commandDocs[' + i + ']: ';
          T.ok(typeof c.cmd === 'string' && c.cmd.length > 0,
               ct + 'has a command token');
          T.ok(typeof c.name === 'string' && c.name.length > 0,
               ct + 'has a name');
          T.ok(typeof c.description === 'string' && c.description.length > 20,
               ct + 'has a real description');
          documented[c.cmd] = true;
        });
        engineCmds.forEach(function (c) {
          T.ok(!!documented[c],
               tag + 'commandDocs documents engine command ' + c);
        });

        // The shared reference renderer's grouping must be lossless:
        // flattening groupParamsByChapter returns every symbol in pack
        // order (both the timing tab and the drill panel depend on it).
        var grouped = DDRD.groupParamsByChapter(pack.timingParams);
        var flat = [];
        grouped.forEach(function (g) {
          g.params.forEach(function (p) { flat.push(p.symbol); });
        });
        T.deepEq(flat, pack.timingParams.map(function (p) { return p.symbol; }),
                 tag + 'groupParamsByChapter is lossless and order-keeping');

        // Turnaround coverage: every pack must be able to label both
        // direction changes for the engine's annotation labels.
        var t = (pack.scenarioTweaks && pack.scenarioTweaks.turnaround) || {};
        T.ok(typeof t.wtr === 'string' && typeof t.rtw === 'string',
             tag + 'scenarioTweaks.turnaround provides wtr and rtw labels');

        // tRTW must exist in every pack (cross-book symbol rule: the
        // drill keys on it even where the spec leaves it unnamed).
        T.ok(!!symbols.tRTW, tag + 'timing table defines tRTW');
        T.ok(!!symbols.tWTR || !!symbols.tWTRL || !!symbols.tWTRS,
             tag + 'timing table defines a write-to-read param');
      });
    }
  });
})();
