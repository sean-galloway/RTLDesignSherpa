// packs/ddr2.js -- DDR2 content pack (JESD79-2F).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/ddr2); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
//
// DDR2 is a FLAT topology: no bank groups, no Stack IDs. Scopes used in
// appliesTo are therefore same_bank / diff_bank / any only.
// tCCD is modeled same-direction only (reads-to-reads, writes-to-writes),
// matching the book's gap sheet - direction changes are governed by the
// turnaround params, which always dominate tCCD there.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'ddr2',
    name: 'DDR2',
    jedec: {
      doc: 'JESD79-2F',
      note: 'DDR2 SDRAM. 4n prefetch, posted CAS (additive latency), ODT, ' +
            'no bank groups. tRTW is a book symbol: the spec gives the ' +
            'read-to-write relation (BL/2 + 2) without naming it.'
    },

    // Simplified drill topology: 8 banks, 8 rows, 8 cols, flat. Real
    // parts: 4 banks (512 Mb and below) or 8 banks (1 Gb+), 1-2 KB pages,
    // x4/x8/x16 organizations.
    topology: {
      hasBankGroups: false,
      groups: 1,
      banksPerGroup: 8,
      banks: 8,
      rows: 8,
      cols: 8,
      sids: 0
    },

    commands: ['ACT', 'PRE', 'RD', 'WR', 'RDA', 'WRA'],

    timingParams: [
      // --- chapter: core (row timings) ---------------------------------
      { symbol: 'tRCD', name: 'Row-to-column delay',
        definition: 'ACT to RD/WR, same bank: time for the row to reach ' +
                    'the sense amps. Posted CAS still must land the ' +
                    'internal CAS at >= tRCD.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tRAS', name: 'Minimum row-open time',
        definition: 'ACT to PRE, same bank: cell data must be restored ' +
                    'before the row closes. 45 ns min, 70 us max.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRP', name: 'Precharge recovery',
        definition: 'PRE to ACT, same bank: sense amps and bitlines ' +
                    'restored. Bin-matched to tRCD.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRC', name: 'Full row cycle',
        definition: 'ACT to ACT, same bank; equals tRAS + tRP by ' +
                    'construction (55-60 ns at DDR2-800).',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRRD', name: 'Activate-to-activate spacing',
        definition: 'ACT to ACT, different banks (no bank groups in ' +
                    'DDR2): limits peak array current. 7.5 ns (1KB page) ' +
                    '/ 10 ns (2KB page).',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_bank' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'At most 4 ACTs in any rolling tFAW-wide window ' +
                    '(8-bank parts). On activate-heavy streams this ' +
                    'usually binds before tRRD does.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRTP', name: 'Read to precharge',
        definition: 'RD to PRE, same bank: the last 4-word read prefetch ' +
                    'must complete internally first. 7.5 ns; command form ' +
                    'AL + BL/2 + max(RU(tRTP), 2) - 2.',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'Last write data to PRE, same bank. 15 ns; programmed ' +
                    'in clocks in MR (WR = RU(tWR/tCK), codes 2-6). ' +
                    'Command form WL + BL/2 + WR.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tDAL', name: 'Write auto-precharge total',
        definition: 'WRA to ACT, same bank: programmed WR plus precharge ' +
                    'before the bank may re-open. Equals WR + tRP in ' +
                    'clocks; also bounded by tRC.',
        chapter: 'core',
        appliesTo: [{ from: 'WRA', to: 'ACT', scope: 'same_bank' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCD', name: 'Column-to-column spacing',
        definition: 'Same-direction column command spacing, any banks: ' +
                    '2 clocks. At BL4 that equals BL/2, so back-to-back ' +
                    'BL4 bursts saturate the DQ bus. Direction changes ' +
                    'are governed by tRTW/tWTR instead.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'any' },
                    { from: 'WR|WRA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tRTW', name: 'Read-to-write turnaround',
        definition: 'Read burst and postamble must clear before the ' +
                    'write preamble. Book symbol - JESD79-2F gives the ' +
                    'relation unnamed: BL/2 + 2 clocks (4 at BL4, 6 at ' +
                    'BL8), any banks.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tWTR', name: 'Write-to-read turnaround',
        definition: 'Last write data must propagate into the sense amps ' +
                    'before a read. 7.5 ns (10 ns at DDR2-400); command ' +
                    'form CL - 1 + BL/2 + RU(tWTR), any banks.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'any' }] },

      // --- chapter: refresh (reference panel; the drill engine does ----
      // --- not emit REF commands, so these never match a question) -----
      { symbol: 'tREFI', name: 'Average refresh interval',
        definition: 'REF to REF, all-bank. 7.8 us at 0-85 C case, 3.9 us ' +
                    'at 85-95 C. Up to 8 REFs may be postponed (9 x tREFI ' +
                    'absolute bound).',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFC', name: 'Refresh cycle time',
        definition: 'REF to next command. Grows steeply with density: ' +
                    '75 ns (256 Mb) to 327.5 ns (4 Gb) - about 4% of all ' +
                    'bus time at 4 Gb.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF|ACT', scope: 'any' }] },
      { symbol: 'tXSRD', name: 'Self-refresh exit to read',
        definition: 'SRX to RD: 200 clocks while the DLL re-locks (same ' +
                    '200-clock rule as init). Non-read commands only need ' +
                    'tXSNR = tRFC + 10 ns.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: 'RD|RDA', scope: 'any' }] }
    ],

    questionBank: [
      { q: 'How many banks does a 1 Gb or larger DDR2 device have?',
        answers: [
          '8 banks, addressed BA0-BA2',
          '4 banks, addressed BA0-BA1',
          '16 banks in two bank groups',
          'It depends on the burst length'
        ],
        chapter: 'organization', hard: false,
        explanation: '1 Gb and larger DDR2 parts have 8 banks (BA0-BA2); 512 Mb and below have 4 (BA0-BA1). DDR2 has NO bank groups - one timing regime covers all banks.',
        source: 'JESD79-2F sec 2.2' },

      { q: 'What does the 4n prefetch mean for the DDR2 array core?',
        answers: [
          'One column access pulls 4 words per DQ internally, so the array core runs at one quarter of the pin data rate and BL4 is the minimum burst',
          'The core runs 4x faster than the pins to keep up',
          'Every command is duplicated 4 times on the CA bus',
          'Four banks must be activated for every read'
        ],
        chapter: 'organization', hard: false,
        explanation: 'The 4n prefetch fetches 4 words per DQ in parallel: the core ambles along at 1/4 the pin rate while the interface serializes the 4 words. BL4 is the minimum burst; BL8 takes two internal fetches.',
        source: 'JESD79-2F sec 2.4' },

      { q: 'On a DDR2 read or write command, what does address bit A10 carry?',
        answers: [
          'The auto-precharge flag (AP) - it is NOT a column address bit',
          'The most significant column bit',
          'The bank-select strobe',
          'The ODT toggle'
        ],
        chapter: 'organization', hard: false,
        explanation: 'A10 on a column command is the auto-precharge flag: AP=1 turns RD into RDA and WR into WRA. Column addressing is A0-A9 (plus A11 on x4 parts).',
        source: 'JESD79-2F sec 3.2' },

      { q: 'How are MR, EMR1, EMR2 and EMR3 selected during an MRS/EMRS command?',
        answers: [
          'By the bank address: BA=00 MR, 01 EMR1, 10 EMR2, 11 EMR3',
          'By A10: high selects the extended registers',
          'By issuing the command twice in a row',
          'EMR2/EMR3 do not exist in DDR2'
        ],
        chapter: 'init', hard: false,
        explanation: 'The register file is selected by BA1:BA0 during the mode-register command. All four must be programmed at init, all banks idle, tMRD apart.',
        source: 'JESD79-2F sec 3.4' },

      { q: 'Where is additive latency (AL) programmed, and what does it do?',
        answers: [
          'EMR1 A5-A3; it delays the internal CAS by AL clocks after the RD/WR command (posted CAS), letting row and column commands pack tighter on the bus',
          'MR A6-A4; it adds clocks to the burst',
          'EMR2 A7; it extends refresh',
          'Any register; AL is just a read-only status'
        ],
        chapter: 'init', hard: true,
        explanation: 'AL lives in EMR1 A5-A3 (0-4, 5 optional). With posted CAS the controller issues RD/WR immediately after ACT and the device holds the column command internally for AL clocks - but the internal CAS still must satisfy tRCD.',
        source: 'JESD79-2F sec 3.4.2' },

      { q: 'On an activate-heavy stream with plenty of banks free, which constraint usually binds first?',
        answers: [
          'tFAW - no more than 4 ACTs in any rolling tFAW-wide window',
          'tRRD - the pairwise ACT spacing',
          'tRC - the same-bank row cycle',
          'tCCD - column spacing'
        ],
        chapter: 'timing', hard: false,
        explanation: 'tRRD paces any two ACTs but tFAW caps any rolling window of four; with many banks to rotate through, tFAW is typically the binding constraint. tRC is same-bank only and tCCD governs columns, not activates.',
        source: 'JESD79-2F sec 3.7' },

      { q: 'After a write with auto-precharge, when may the same bank be re-activated?',
        answers: [
          'After tDAL = WR + tRP clocks (and tRC must also be met)',
          'After tWR alone',
          'After tRP alone',
          'Immediately - auto-precharge is free'
        ],
        chapter: 'timing', hard: true,
        explanation: 'tDAL chains the programmed write recovery (WR, in clocks from MR) and the precharge time: WRA -> ACT >= WR + tRP, with tRC as an additional floor.',
        source: 'JESD79-2F sec 3.8' },

      { q: 'Why can back-to-back BL4 bursts saturate the DDR2 data bus?',
        answers: [
          'tCCD = 2 clocks exactly equals BL/2 = 2 clocks of bus occupancy per BL4 burst, so a new column command can issue every 2 clocks with no gap',
          'Because ODT is always on',
          'Because BL4 bursts can be interrupted freely',
          'Because tFAW does not apply to reads'
        ],
        chapter: 'timing', hard: false,
        explanation: 'A BL4 burst occupies BL/2 = 2 clocks of DQ. Same-direction commands may issue every tCCD = 2 clocks, so the second burst\'s data follows the first with zero bubble. BL8 leaves no such luck at tCCD = 2 (4-clock occupancy).',
        source: 'JESD79-2F sec 3.6.1' },

      { q: 'What is the DDR2 read-to-write command spacing?',
        answers: [
          'BL/2 + 2 clocks - 4 at BL4, 6 at BL8 (this book calls the parameter tRTW; JESD79-2F states the relation without naming it)',
          'tCCD = 2 clocks, same as reads',
          'CL - 1 + BL/2 + RU(tWTR)',
          'One full tRC'
        ],
        chapter: 'timing', hard: true,
        explanation: 'The read burst plus its postamble must clear the pins before the write preamble: RD -> WR = BL/2 + 2 clocks. (The CL-1+BL/2+RU(tWTR) formula is the WRITE-to-read direction.)',
        source: 'JESD79-2F sec 3.6.3' },

      { q: 'Which ODT termination value is MANDATORY at DDR2-800 (optional below)?',
        answers: [
          '50 ohm',
          '75 ohm',
          '150 ohm',
          'ODT off'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'EMR1 programs Rtt to off/75/150/50 ohm (A6, A2). The 50 ohm option is required at DDR2-800 signaling rates; below that it is optional.',
        source: 'JESD79-2F sec 3.4.2' },

      { q: 'A BL4 read is in flight. Which commands may legally interrupt it?',
        answers: [
          'None - a BL4 burst is never interruptible, in either direction, by anything',
          'Another read, on any even clock',
          'A write, if tRTW is met',
          'Any command with auto-precharge'
        ],
        chapter: 'commands', hard: false,
        explanation: 'BL4 bursts cannot be interrupted at all. Only BL8 may be cut - and only by a same-direction command at the 4-word (prefetch) boundary. DDR2 has no Burst Terminate command.',
        source: 'JESD79-2F sec 3.6.4' },

      { q: 'How many refresh commands may a DDR2 controller postpone, and what does that bound?',
        answers: [
          'Up to 8, so the worst-case gap between two REFs is 9 x tREFI',
          'Up to 2, bounded by tRFC',
          'None - tREFI is a hard per-command deadline',
          'Unlimited, if temperature is low'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'Posting up to 8 refreshes buys scheduling freedom (finish a burst sequence or tFAW window first), but the postponed REFs land as a cluster later and the 9 x tREFI bound still holds.',
        source: 'JESD79-2F sec 3.9' },

      { q: 'Why does exiting self-refresh to a READ take so much longer than to a non-read command?',
        answers: [
          'Reads need the DLL re-locked: tXSRD = 200 clocks, while non-read commands only wait tXSNR = tRFC + 10 ns',
          'Reads are lower priority in the arbiter',
          'The mode registers must be reprogrammed first',
          'ODT calibration runs before the first read'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'The DLL shuts down in self-refresh. Non-read commands can go after tXSNR, but a read needs the strobes aligned - the same 200-clock DLL relock rule as initialization.',
        source: 'JESD79-2F sec 3.10' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: [],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
