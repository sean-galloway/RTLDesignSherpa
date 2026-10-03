// packs/ddr3.js -- DDR3 content pack (JESD79-3F).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/ddr3); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
//
// DDR3 is a FLAT topology: no bank groups, no Stack IDs. Scopes used in
// appliesTo are therefore same_bank / diff_bank / any only.
// tCCD is modeled same-direction only (reads-to-reads, writes-to-writes),
// matching the book's gap sheet - direction changes are governed by the
// turnaround params, which always dominate tCCD there.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'ddr3',
    name: 'DDR3',
    jedec: {
      doc: 'JESD79-3F',
      note: 'DDR3 SDRAM. 8n prefetch, BL8/BC4 burst chop, dynamic ODT, ' +
            'write leveling, ZQ calibration, reset pin; flat 8 banks.'
    },

    // Simplified drill topology: 8 banks, 8 rows, 8 cols, flat. Real
    // parts: 512 Mb-8 Gb, all with 8 banks (BA0-BA2), 1-2 KB pages,
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
                    'internal CAS at >= tRCD. 10-15 ns by speed bin.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tRAS', name: 'Minimum row-open time',
        definition: 'ACT to PRE, same bank: cell data must be restored ' +
                    'before the row closes. 36-37.5 ns min, max 9 x tREFI.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRP', name: 'Precharge recovery',
        definition: 'PRE to ACT, same bank: sense amps and bitlines ' +
                    'restored. Bin-matched to tRCD; PREA uses the same ' +
                    'tRP as PRE (unlike DDR2).',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRC', name: 'Full row cycle',
        definition: 'ACT to ACT, same bank; equals tRAS + tRP by ' +
                    'construction (46.5-52.5 ns by bin).',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRRD', name: 'Activate-to-activate spacing',
        definition: 'ACT to ACT, different banks (no bank groups in ' +
                    'DDR3): limits peak array current. max(4 nCK, X ns), ' +
                    'e.g. 10 ns at DDR3-800 down to 5 ns at 1866/2133.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_bank' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'At most 4 ACTs in any rolling tFAW-wide window ' +
                    '(8-bank parts). On activate-heavy streams this ' +
                    'usually binds before tRRD does. 25-50 ns by speed/page.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRTP', name: 'Read to precharge',
        definition: 'RD to PRE, same bank: the second 4-word half of the ' +
                    '8n prefetch must finish internally first. ' +
                    'max(4 nCK, 7.5 ns); command form AL + BL/2 + ' +
                    'RU(tRTP).',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'First CK after the last write data to PRE, same bank. ' +
                    '15 ns; programmed in clocks in MR0 (WR codes 5-16). ' +
                    'Command form WL + BL/2 + WR.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tDAL', name: 'Write auto-precharge total',
        definition: 'WRA to ACT, same bank: programmed WR plus precharge ' +
                    'before the bank may re-open. Equals WL + BL/2 + WR + ' +
                    'tRP clocks; also bounded by tRC.',
        chapter: 'core',
        appliesTo: [{ from: 'WRA', to: 'ACT', scope: 'same_bank' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCD', name: 'Column-to-column spacing',
        definition: 'Same-direction column command spacing, any banks: ' +
                    '4 clocks. At BL8 that equals BL/2 = 4 clocks of bus ' +
                    'occupancy, so back-to-back BL8 bursts saturate the DQ ' +
                    'bus. Direction changes are governed by tRTW/tWTR instead.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'any' },
                    { from: 'WR|WRA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tRTW', name: 'Read-to-write turnaround',
        definition: 'Read burst and postamble must clear before the ' +
                    'write preamble. Book symbol - JESD79-3F gives the ' +
                    'relation unnamed: RL + tCCD + 2 - WL at BL8, any banks.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tWTR', name: 'Write-to-read turnaround',
        definition: 'Last write data must propagate into the sense amps ' +
                    'before a read. max(4 nCK, 7.5 ns); command form ' +
                    'WL + BL/2 + RU(tWTR), any banks.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'any' }] },

      // --- chapter: init (reference panel; MRS is not an engine cmd) ---
      { symbol: 'tMRD', name: 'Mode-register command spacing',
        definition: 'MRS to MRS. 4 nCK minimum between consecutive mode ' +
                    'register writes during init. Panel-only: the drill ' +
                    'engine does not emit MRS commands.',
        chapter: 'init',
        appliesTo: [{ from: 'MRS', to: 'MRS', scope: 'any' }] },
      { symbol: 'tMOD', name: 'Mode-register update delay',
        definition: 'MRS to any non-MRS command. max(12 nCK, 15 ns). ' +
                    'Also the quiet window after which new RTT values are ' +
                    'reliable. Panel-only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRS', to: '*', scope: 'any' }] },
      { symbol: 'tDLLK', name: 'DLL lock time',
        definition: 'DLL reset (MR0 A8 = 1) to a command that needs a ' +
                    'locked DLL, such as RD or synchronous ODT. 512 nCK. ' +
                    'Panel-only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRS', to: 'RD|RDA', scope: 'any' }] },

      // --- chapter: refresh (reference panel; REF/SRX are engine-only) -
      { symbol: 'tREFI', name: 'Average refresh interval',
        definition: 'REF to REF, all-bank average. 7.8 us at 0-85 C case, ' +
                    '3.9 us at 85-95 C. Up to 8 REFs may be postponed ' +
                    '(9 x tREFI absolute bound); up to 8 may be pulled in. ' +
                    'Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFC', name: 'Refresh cycle time',
        definition: 'REF to next command. Grows with density: 90 ns ' +
                    '(512 Mb), 110 ns (1 Gb), 160 ns (2 Gb), 260 ns ' +
                    '(4 Gb), 350 ns (8 Gb). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF|ACT', scope: 'any' }] },
      { symbol: 'tXS', name: 'Self-refresh exit to non-DLL commands',
        definition: 'SRX to ACT, PRE, MRS, REF or ZQ. max(5 nCK, ' +
                    'tRFC(min) + 10 ns). Commands that need a locked DLL ' +
                    '(such as RD) wait the additional tXSDLL = tDLLK. ' +
                    'Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: 'ACT|PRE|MRS|REF', scope: 'any' }] },
      { symbol: 'tXP', name: 'Power-down exit',
        definition: 'PDX to any valid command when the DLL was kept on. ' +
                    'max(3 nCK, 6-7.5 ns by speed). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] }
    ],

    questionBank: [
      { q: 'What does the 8n prefetch imply for the DDR3 array core?',
        answers: [
          'One column access pulls 8 words per DQ from the array, so the core runs at one eighth of the pin data rate and BL8 is the natural burst',
          'The core runs 8x faster than the pins',
          'Every read must be followed by eight identical commands',
          'Only x16 devices can use the 8n prefetch'
        ],
        chapter: 'organization', hard: false,
        explanation: 'The 8n prefetch fetches 8 words per DQ in parallel; the array core runs at 1/8 the pin data rate. BL8 uses all 8 words; BC4 uses the first 4 and discards the rest.',
        source: 'JESD79-3F sec 2.11' },

      { q: 'How does a DDR3 read or write command select between BL8 and BC4 on-the-fly?',
        answers: [
          'A12/BC#: high means BL8, low means BC4 (when OTF is enabled in MR0)',
          'A10: high selects BL8, low selects BC4',
          'The bank address pins encode the burst length',
          'A12 is the most-significant column address bit'
        ],
        chapter: 'organization', hard: false,
        explanation: 'A12/BC# is the burst-chop control: 1 = BL8, 0 = BC4, valid only when MR0 A1:A0 = 01 (on-the-fly). When BL8 or BC4 is fixed in MR0, A12 is ignored. A10 is the auto-precharge flag, not a column bit.',
        source: 'JESD79-3F sec 3.2' },

      { q: 'During DDR3 initialization, in what order must the mode registers be loaded?',
        answers: [
          'MR2, then MR3, then MR1, then MR0 (with DLL reset), then ZQCL',
          'MR0, then MR1, then MR2, then MR3',
          'Any order, as long as all four are written',
          'MR1, then MR0, then MR2, then MR3'
        ],
        chapter: 'init', hard: false,
        explanation: 'The fixed init sequence after CKE high is MRS(MR2), MRS(MR3), MRS(MR1), MRS(MR0 with A8=1 to reset the DLL), then ZQCL, then wait tDLLK and tZQinit.',
        source: 'JESD79-3F sec 3.3.1' },

      { q: 'Which mode register holds each of these fields: CL, CWL, AL/write-leveling/DLL-enable, and MPR enable?',
        answers: [
          'CL in MR0, CWL in MR2, AL/write-leveling/DLL-enable in MR1, MPR enable in MR3',
          'CL in MR1, CWL in MR0, AL in MR2, MPR in MR1',
          'All latency fields are in MR0',
          'CL in MR2, CWL in MR1, write-leveling in MR0, MPR in MR2'
        ],
        chapter: 'init', hard: true,
        explanation: 'MR0 carries CL and WR; MR2 carries CWL, dynamic ODT (Rtt_WR), SRT/ASR; MR1 carries DLL enable, AL, write-leveling enable, Rtt_NOM; MR3 carries MPR enable.',
        source: 'JESD79-3F sec 3.4' },

      { q: 'What is the DDR3 write-latency formula?',
        answers: [
          'WL = AL + CWL',
          'WL = RL - 1',
          'WL = CL - 1',
          'WL = AL + CL'
        ],
        chapter: 'init', hard: true,
        explanation: 'DDR3 programs CWL independently in MR2, so WL = AL + CWL. The WL = RL - 1 rule belongs to DDR2; RL = AL + CL still applies to reads.',
        source: 'JESD79-3F sec 3.4.3' },

      { q: 'On a DDR3 column command, what is address bit A10 used for?',
        answers: [
          'The auto-precharge flag (AP): A10=1 turns RD into RDA and WR into WRA',
          'The most-significant column bit',
          'BL8 vs BC4 selection',
          'The bank-group selector'
        ],
        chapter: 'commands', hard: false,
        explanation: 'A10 carries the auto-precharge flag on RD/WR commands. Column addressing is A0-A9 (plus extra bits on some densities). BL8/BC4 is A12/BC#, and DDR3 has no bank groups.',
        source: 'JESD79-3F sec 3.2' },

      { q: 'When DDR3 burst mode is fixed in MR0, what happens to A12/BC# during a column command?',
        answers: [
          'A12/BC# is ignored because the burst length is already fixed',
          'A12 still selects BL8 vs BC4 on every command',
          'A12 becomes a regular column address bit',
          'The command is illegal if A12 is high'
        ],
        chapter: 'commands', hard: false,
        explanation: 'On-the-fly burst control only works when MR0 A1:A0 = 01. With fixed BL8 (00) or fixed BC4 (10), A12/BC# is ignored for burst selection.',
        source: 'JESD79-3F sec 3.4.1' },

      { q: 'Why can back-to-back BL8 read bursts saturate the DDR3 data bus?',
        answers: [
          'tCCD = 4 clocks exactly equals BL/2 = 4 clocks of bus occupancy per BL8 burst',
          'Because BL8 bursts can be interrupted freely',
          'Because tFAW does not apply to reads',
          'Because ODT is always on during reads'
        ],
        chapter: 'timing', hard: false,
        explanation: 'A BL8 burst occupies BL/2 = 4 clocks of DQ. Same-direction commands may issue every tCCD = 4 clocks, so the next burst follows immediately. BC4 still pays the full 4-clock tCCD even though it only transfers 2 clocks of data.',
        source: 'JESD79-3F sec 4.13' },

      { q: 'Which direction change does the book symbol tRTW describe?',
        answers: [
          'Read-to-write: the read burst and postamble must clear before the write preamble',
          'Write-to-read: last write data must leave the input path before a read',
          'Read-to-read on different banks',
          'Write-to-write on different banks'
        ],
        chapter: 'timing', hard: true,
        explanation: 'tRTW is read-to-write. The spec does not name it; the book adds the symbol for cross-technology comparison. tWTR is the write-to-read direction, and tCCD covers same-direction column commands.',
        source: 'JESD79-3F sec 4.14' },

      { q: 'Which timing parameter separates a write burst from the next read command, and which separates write data from precharge?',
        answers: [
          'tWTR separates WR -> RD; tWR separates last write data -> PRE',
          'tWR separates WR -> RD; tWTR separates last write data -> PRE',
          'tRTW separates both transitions',
          'tCCD separates both transitions'
        ],
        chapter: 'timing', hard: true,
        explanation: 'tWTR is the write-to-read turnaround (last data into the array before a read). tWR is write recovery (last data committed to cells before precharge). tRTW is read-to-write, and tCCD is same-direction column spacing.',
        source: 'JESD79-3F sec 4.14' },

      { q: 'What is the difference between Rtt_NOM and Rtt_WR in DDR3?',
        answers: [
          'Rtt_NOM is the normal termination value in MR1; Rtt_WR is a separate stronger/weaker write termination in MR2 used by dynamic ODT',
          'Rtt_NOM is for writes, Rtt_WR is for reads',
          'They are two names for the same register field',
          'Rtt_WR is only used during initialization'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'Rtt_NOM lives in MR1 and is the default termination when ODT is asserted. Rtt_WR lives in MR2 and is the value dynamic ODT switches to during writes. Dynamic ODT requires the DLL to be on.',
        source: 'JESD79-3F sec 5.2' },

      { q: 'What problem does DDR3 write leveling solve?',
        answers: [
          'Fly-by CA/CK routing makes CK arrive at each DRAM at a different time relative to DQS; write leveling aligns DQS to CK per rank',
          'It calibrates the output driver impedance against the ZQ resistor',
          'It selects the optimal CAS latency',
          'It refreshes rows during initialization'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'Write leveling (MR1 A7 = 1) lets the controller sweep DQS delay while each DRAM feeds back the sampled CK level on DQ, compensating for fly-by skew. ZQ calibration handles impedance, not timing.',
        source: 'JESD79-3F sec 4.8' },

      { q: 'What is the purpose of the ZQ pin and the ZQCL/ZQCS commands?',
        answers: [
          'The ZQ pin bonds to a 240 ohm RZQ resistor; ZQCL is a long calibration used at init, ZQCS is a shorter periodic calibration',
          'ZQ selects the zero-page row address',
          'ZQCL refreshes the entire array, ZQCS refreshes one bank',
          'The ZQ pin carries the write data mask'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'ZQ calibration trims output driver impedance and ODT against an external 240 ohm resistor. ZQCL is required at init and takes tZQinit; ZQCS is a periodic short correction taking tZQCS.',
        source: 'JESD79-3F sec 5.5' },

      { q: 'How many refresh commands may be postponed or pulled in, and what bounds them?',
        answers: [
          'Up to 8 postponed (max gap 9 x tREFI), up to 8 pulled in, at most 16 REFs in any 2 x tREFI window',
          'Up to 2 postponed, no pulling in allowed',
          'Unlimited postponement if temperature is low',
          'Up to 16 postponed and 16 pulled in per tREFI'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'DDR3 allows up to 8 REFs to be postponed, so the worst-case gap between REFs is 9 x tREFI. Up to 8 may be pulled in early, but no more than 16 REFs may occur in any 2 x tREFI window.',
        source: 'JESD79-3F sec 4.15' },

      { q: 'Which statement about DDR3 refresh and self-refresh is correct?',
        answers: [
          'DDR3 has only all-bank refresh (no per-bank refresh), and self-refresh temperature range is selected by SRT/ASR bits in MR2',
          'DDR3 supports per-bank refresh to hide refresh latency',
          'Self-refresh disables the DLL automatically but SRT is in MR1',
          'Refresh commands can be issued to individual banks using BA0-BA2'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'DDR3 REF is always all-bank; there is no per-bank refresh command. SRT (MR2 A7) and ASR (MR2 A6) configure the self-refresh temperature range. The DLL does shut down in self-refresh.',
        source: 'JESD79-3F sec 4.15, 4.16' }
    ],

    commandDocs: [
      { cmd: 'ACT', name: 'Bank Activate',
        description: 'Opens row R in bank B (the row is copied into the ' +
                     'bank\'s sense amps). Required before any RD/WR to ' +
                     'that bank. Spacing: tRCD to the first column command, ' +
                     'tRRD to the next ACT, tFAW across any four.' },
      { cmd: 'PRE', name: 'Precharge (one bank)',
        description: 'Closes the open row of the bank selected by BA, ' +
                     'restoring data to the array. A10 = 0 selects one bank. ' +
                     'The bank is ready for a new ACT after tRP.' },
      { cmd: 'RD', name: 'Read',
        description: 'Bursts BL words from the open row starting at the ' +
                     'given column; data appears RL = AL + CL clocks after ' +
                     'the command. A10 = 0 (no auto-precharge). A12/BC# ' +
                     'selects BL8 or BC4 when OTF is enabled.' },
      { cmd: 'RDA', name: 'Read with Auto-Precharge',
        description: 'RD with A10 = 1: the bank precharges itself once ' +
                     'tRAS and tRTP are met. Re-activation waits tRP past ' +
                     'the internal precharge, and tRC from the old ACT.' },
      { cmd: 'WR', name: 'Write',
        description: 'Bursts BL words into the open row; first data is ' +
                     'captured WL = AL + CWL clocks after the command. ' +
                     'A10 = 0. A12/BC# selects BL8 or BC4 when OTF is ' +
                     'enabled.' },
      { cmd: 'WRA', name: 'Write with Auto-Precharge',
        description: 'WR with A10 = 1: the bank precharges itself after ' +
                     'write recovery. Next ACT waits WL + BL/2 + WR + tRP ' +
                     '(and tRC).' },
      { cmd: 'MRS', name: 'Mode Register Set',
        description: 'Writes MR0, MR1, MR2 or MR3, selected by BA2:BA0. ' +
                     'All banks idle, tMRD between writes, tMOD before any ' +
                     'non-MRS command. Carries CL, CWL, AL, BL, WR, DLL ' +
                     'enable, write leveling, Rtt_NOM, Rtt_WR and MPR.' },
      { cmd: 'REF', name: 'Refresh',
        description: 'One internal all-bank refresh step (address counter ' +
                     'is internal). All banks must be precharged first; ' +
                     'the device is busy for tRFC. Average rate tREFI; up ' +
                     'to 8 may be postponed (9 x tREFI worst gap), up to 8 ' +
                     'pulled in, at most 16 per 2 x tREFI.' },
      { cmd: 'ZQCL/ZQCS', name: 'ZQ Calibration Long / Short',
        description: 'ZQCL performs a full calibration of output driver ' +
                     'and ODT impedance against the external 240 ohm ZQ ' +
                     'resistor; required at init (tZQinit). ZQCS is a short ' +
                     'periodic update (tZQCS). All banks idle and tRP met.' },
      { cmd: 'SRE/SRX', name: 'Self-Refresh Entry / Exit',
        description: 'Entry: REF encoding with CKE falling, all banks idle, ' +
                     'ODT off - the DRAM refreshes itself with the clock ' +
                     'stopped. Exit: tXS to non-DLL commands, tXSDLL = 512 ' +
                     'nCK to reads (DLL re-lock). Issue at least one REF ' +
                     'before re-entering.' },
      { cmd: 'PDE/PDX', name: 'Power-Down Entry / Exit',
        description: 'CKE low parks the device in precharge or active ' +
                     'power-down. Precharge PD has fast (MR0 A12 = 1, DLL ' +
                     'on) and slow (MR0 A12 = 0, DLL off) exit modes. Exit ' +
                     'to any command: tXP; slow exit to DLL commands: tXPDLL. ' +
                     'No refresh inside; stay bounded by tREFI rules.' },
      { cmd: 'NOP/DES', name: 'No Operation / Deselect',
        description: 'Filler cycles that keep the bus valid while timing ' +
                     'windows drain. Required through mode-register, ' +
                     'self-refresh-exit and power-down windows.' },
      { cmd: 'MPR', name: 'Multi-Purpose Register Read',
        description: 'Enter via MR3 A2 = 1 after precharging all banks; ' +
                     'only RD/RDA are legal until MR3 A2 is cleared. The ' +
                     'MPR outputs a fixed training pattern for read timing ' +
                     'alignment. RDA auto-precharge is ignored in MPR mode.' },
      { cmd: 'RESET', name: 'Asynchronous Reset',
        description: 'RESET# low overrides the command bus, aborts any ' +
                     'operation, and forces outputs to High-Z. After ' +
                     'RESET# rises the normal power-up or stable-power ' +
                     'reset sequence must be followed before normal traffic.' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: [],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
