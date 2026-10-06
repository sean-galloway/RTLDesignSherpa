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
      T.ok(bg.indexOf('2 bank groups (BG0, BG1)') !== -1,
           'BG topo enumerates the group ids');
      T.ok(bg.indexOf('8 banks (B0-B7)') !== -1,
           'BG topo spells the bank range');
      T.ok(bg.indexOf('8 rows (R0-R7)') !== -1 &&
           bg.indexOf('8 columns (C0-C7)') !== -1,
           'BG topo spells the row/column ranges');
      T.ok(bg.indexOf('no bank groups') === -1,
           'BG topo does not claim flatness');
      T.ok(bg.indexOf('SID') === -1,
           'BG topo without stacks omits the SID clause');

      // Flat, no stacks (ddr2-style).
      var flat = DDRD.assumptionsText({ hasBankGroups: false, groups: 1,
                                        banksPerGroup: 8, banks: 8,
                                        rows: 8, cols: 8, sids: 0 });
      T.ok(flat.indexOf('8 banks (B0-B7, no bank groups)') !== -1,
           'flat topo says so explicitly inside the bank range');
      T.ok(flat.indexOf('8 rows (R0-R7)') !== -1,
           'flat topo spells the row range');

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

      // -- AXI-style id field ------------------------------------------------
      // The id renders between the op and any sid, and only when present,
      // so id-less drill text (and its dedup keys) are unchanged.
      T.eq(DDRD.format_req(DDRD.make_req('RD', 1, 2, 3)), 'RD B1 R2 C3',
           'format_req without id is unchanged');
      T.eq(DDRD.format_req(DDRD.make_req('RD', 1, 2, 3, null, 2)),
           'RD id2 B1 R2 C3', 'format_req carries the id after the op');
      T.eq(DDRD.format_req(DDRD.make_req('WR', 1, 2, 3, 1, 0)),
           'WR id0 S1 B1 R2 C3', 'id renders before the sid');
      T.eq(DDRD.format_req(DDRD.make_req('RD', 1, 2, 3, 0, 0)),
           'RD id0 S0 B1 R2 C3', 'id 0 is real (falsy but not null)');

      T.eq(DDRD.format_cmd(DDRD.make_cmd('ACT', 1, 2, null, null, 3)),
           'ACT id3 B1 R2', 'format_cmd ACT carries the id');
      T.eq(DDRD.format_cmd(DDRD.make_cmd('RD', 1, null, 5, null, 1)),
           'RD id1 B1 C5', 'format_cmd column cmd carries the id');
      T.eq(DDRD.format_cmd(DDRD.make_cmd('PRE', 1, null, null, null, 1)),
           'PRE id1 B1', 'format_cmd PRE carries the id');
      T.eq(DDRD.format_cmd(DDRD.make_cmd('RD', 1, null, 5)),
           'RD B1 C5', 'format_cmd without id is unchanged');
    }
  });
})();
