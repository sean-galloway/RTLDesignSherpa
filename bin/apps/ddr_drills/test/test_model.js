// test_model.js -- model.js helpers: the artificial-geometry disclaimer
// text shown at the top of every drill and the sandbox. Verbatim for the
// three topology flavors the packs ship (bank-grouped, flat, flat+SIDs).
var SUITES = (typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES ||
             ((typeof window !== 'undefined' ? window : globalThis).DDRD_TEST_SUITES = []);

(function () {
  'use strict';

  var DDRD = globalThis.DDRD;

  SUITES.push({
    name: 'model',
    run: function (T) {
      T.ok(typeof DDRD.assumptionsText === 'function',
           'assumptionsText registered on DDRD');

      // Bank-grouped, no stacks (ddr4-style).
      var bg = DDRD.assumptionsText({ hasBankGroups: true, groups: 2,
                                      banksPerGroup: 4, banks: 8,
                                      rows: 8, cols: 8, sids: 0 });
      T.ok(bg.indexOf('2 bank groups of 4 banks') !== -1,
           'BG topo names the group count');
      T.ok(bg.indexOf('8 rows, 8 columns') !== -1,
           'BG topo names rows and columns');
      T.ok(bg.indexOf('(no bank groups)') === -1,
           'BG topo does not claim flatness');
      T.ok(bg.indexOf('SID') === -1,
           'BG topo without stacks omits the SID clause');

      // Flat, no stacks (ddr2-style).
      var flat = DDRD.assumptionsText({ hasBankGroups: false, groups: 1,
                                        banksPerGroup: 8, banks: 8,
                                        rows: 8, cols: 8, sids: 0 });
      T.ok(flat.indexOf('8 banks (no bank groups)') !== -1,
           'flat topo says so explicitly');
      T.ok(flat.indexOf('8 rows, 8 columns') !== -1,
           'flat topo names rows and columns');

      // Flat with stacks (hbm2-style): the SID clause rides along.
      var sid = DDRD.assumptionsText({ hasBankGroups: false, groups: 1,
                                       banksPerGroup: 8, banks: 8,
                                       rows: 8, cols: 8, sids: 2 });
      T.ok(sid.indexOf('per stack (SID)') !== -1,
           'stacked topo notes the geometry repeats per SID');

      // Every shipped pack produces a non-empty note naming its real
      // geometry (guards against topo fields drifting from the text).
      ['hbm4', 'ddr2', 'lpddr2', 'ddr3', 'lpddr3', 'ddr4', 'lpddr4',
       'ddr5', 'lpddr5', 'hbm2', 'hbm3'].forEach(function (id) {
        var pack = DDRD.getPack(id);
        var t = DDRD.assumptionsText(pack.topology);
        T.ok(t.indexOf(String(pack.topology.rows) + ' rows') !== -1 &&
             t.indexOf(String(pack.topology.cols) + ' columns') !== -1,
             id + ' disclaimer names its geometry');
      });
    }
  });
})();
