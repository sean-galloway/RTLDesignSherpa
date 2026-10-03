// packs/ddr4.js -- DDR4 content pack (JESD79-4D).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/ddr4); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
//
// DDR4 is the first mainstream pack with bank groups. Scopes used:
// same_bank / same_group / diff_group / any. The drill model uses 2 BG x 4
// banks; real x8 parts have 4 BG x 4 banks.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'ddr4',
    name: 'DDR4',
    jedec: {
      doc: 'JESD79-4D',
      note: 'DDR4 SDRAM. Bank groups with short/long (S/L) timing splits; ' +
            'fine-granularity refresh (FGR); read/write DBI; write CRC; ' +
            'CA parity; 1.2 V VDD/VDDQ plus 2.5 V VPP.'
    },

    // Simplified drill topology: 2 bank groups of 4 banks, 8 rows, 8 cols.
    // Real x4/x8 parts have 4 groups of 4 banks; x16 parts have 2 groups.
    topology: {
      hasBankGroups: true,
      groups: 2,
      banksPerGroup: 4,
      banks: 8,
      rows: 8,
      cols: 8,
      sids: 0
    },

    commands: ['ACT', 'PRE', 'RD', 'WR', 'RDA', 'WRA'],

    timingParams: [
      // --- chapter: core (row timings) ---------------------------------
      { symbol: 'tRCD', name: 'Row-to-column delay',
        definition: 'ACT to RD/WR/RDA/WRA, same bank. The row must reach the ' +
                    'sense amps before a column command is legal; nCK per ' +
                    'speed bin (10 at DDR4-1600 up to 24 at DDR4-3200).',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tRP', name: 'Precharge recovery',
        definition: 'PRE to ACT, same bank. Sense amps and bitlines restore ' +
                    'before the bank may re-open; bin-matched to tRCD. ' +
                    'All-bank PRE uses the same tRP as per-bank PRE.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRAS', name: 'Minimum row-open time',
        definition: 'ACT to PRE, same bank. Cell data must be restored ' +
                    'before the row closes; 28-52 nCK by speed, max 9 x tREFI.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRC', name: 'Full row cycle',
        definition: 'ACT to ACT, same bank; equals tRAS + tRP by construction.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRRDS', name: 'Activate spacing, different bank groups',
        definition: 'ACT to ACT across bank groups. 4 nCK (all bins); the ' +
                    'fast path that lets interleaved activates keep pace.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_group' }] },
      { symbol: 'tRRDL', name: 'Activate spacing, same bank group',
        definition: 'ACT to ACT, different banks in one group. 5-11 nCK by ' +
                    'organization and speed; same-group activates share local ' +
                    'row resources and must be spaced wider than tRRDS.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_group' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'No more than 4 ACT commands in any rolling tFAW-wide ' +
                    'window. 16-48 nCK by speed; independent of bank group.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRTP', name: 'Read to precharge',
        definition: 'RD/RDA to PRE, same bank. The internal analog read must ' +
                    'finish before the row closes; max(4 nCK, 7.5 ns).',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'WR/WRA to PRE, same bank. Last write data must be ' +
                    'committed to cells before precharge; 15 ns, programmed ' +
                    'as nWR in MR0.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCDS', name: 'Column spacing, different bank groups',
        definition: 'Column command to column command across groups. 4 nCK; ' +
                    'at BL8 this equals BL/2, so two interleaved groups can ' +
                    'saturate the DQ bus.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'diff_group' }] },
      { symbol: 'tCCDL', name: 'Column spacing, same bank group',
        definition: 'Column command to column command inside one group. ' +
                    '5-8 nCK programmed in MR0 A[12:10]; a single-group ' +
                    'stream cannot fill the bus no matter how many banks it has.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'same_group' },
                    { from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tRTW', name: 'Read-to-write turnaround',
        definition: 'Book symbol - JESD79-4D gives the relation unnamed. ' +
                    'The read burst and postamble must clear before the write ' +
                    'preamble; command gap = RL - WL + BL/2 + 1 + RU(tWPRE).',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tWTRS', name: 'Write-to-read, different bank groups',
        definition: 'Last write data to internal read across bank groups. ' +
                    'max(2 nCK, 2.5 ns); the value is speed-dependent, not ' +
                    'universally 2 clocks.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'diff_group' }] },
      { symbol: 'tWTRL', name: 'Write-to-read, same bank group',
        definition: 'Last write data to internal read inside one group. ' +
                    'max(4 nCK, 7.5 ns); 6-12 nCK by speed.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'same_group' },
                    { from: 'WR|WRA', to: 'RD|RDA', scope: 'same_bank' }] },

      // --- chapter: init (reference panel; MRS is not an engine cmd) ---
      { symbol: 'tMRD', name: 'Mode-register command spacing',
        definition: 'MRS to MRS. 8 nCK minimum between consecutive mode ' +
                    'register writes during init. Panel-only: the drill ' +
                    'engine does not emit MRS commands.',
        chapter: 'init',
        appliesTo: [{ from: 'MRS', to: 'MRS', scope: 'any' }] },
      { symbol: 'tMOD', name: 'Mode-register update delay',
        definition: 'MRS to any non-MRS command. max(24 nCK, 15 ns). Also ' +
                    'the quiet window after which new RTT values are reliable. ' +
                    'Panel-only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRS', to: '*', scope: 'any' }] },
      { symbol: 'tDLLK', name: 'DLL lock time',
        definition: 'DLL reset (MR0 A8 = 1) to a command that needs a locked ' +
                    'DLL, such as RD or synchronous ODT. 597/768/1024 nCK by ' +
                    'speed, programmed via MR6. Panel-only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRS', to: 'RD|RDA', scope: 'any' }] },

      // --- chapter: refresh (reference panel; REF/SRX are engine-only) -
      { symbol: 'tREFI1', name: 'Average refresh interval, 1x mode',
        definition: 'REF to REF, all-bank average in fixed 1x mode. 7.8 us ' +
                    'at normal temperature, halved above 85 C. FGR 2x and 4x ' +
                    'modes use tREFI1/2 and tREFI1/4. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFC1', name: 'Refresh cycle time, 1x mode',
        definition: 'REF to next command in fixed 1x mode. 160/260/350/450 ns ' +
                    'by density (2/4/8/16 Gb). FGR 2x/4x use shorter ' +
                    'tRFC2/tRFC4. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'any' }] },
      { symbol: 'tCKE', name: 'Minimum CKE pulse width',
        definition: 'Minimum high or low pulse width on CKE. max(3 nCK, 5 ns). ' +
                    'Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] },
      { symbol: 'tXP', name: 'Power-down exit',
        definition: 'PDX to any valid command when the DLL was kept on. ' +
                    'max(4 nCK, 6 ns). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] },
      { symbol: 'tXS', name: 'Self-refresh exit to non-DLL commands',
        definition: 'SRX to ACT, PRE, MRS, or REF. max(tRFC1(min) + 10 ns) ' +
                    'per bin; commands that need a locked DLL (such as RD) ' +
                    'wait the additional tXSDLL = tDLLK. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: 'ACT|PRE|MRS|REF', scope: 'any' }] }
    ],

    questionBank: [
      { q: 'What is the headline organization change that distinguishes DDR4 from DDR3?',
        answers: [
          'Banks are arranged in bank groups, and several timings split into short (different group) and long (same group) forms',
          'The prefetch doubles from 8n to 16n',
          'The supply voltage drops from 1.5 V to 0.9 V',
          'Per-bank refresh replaces all-bank refresh'
        ],
        chapter: 'organization', hard: false,
        explanation: 'DDR4 keeps the 8n prefetch and adds bank groups (4 groups of 4 banks on x4/x8, 2 groups on x16). This creates tRRDS/tRRDL, tCCDS/tCCDL, and tWTRS/tWTRL. It also keeps all-bank refresh and adds FGR, not per-bank refresh.',
        source: 'JESD79-4D sec 2.8' },

      { q: 'How many independent bank groups does a real DDR4 x8 device contain?',
        answers: [
          'Four bank groups of four banks each, for 16 banks total',
          'Two bank groups of four banks each, for 8 banks total',
          'Eight banks with no groups',
          'One bank group of eight banks'
        ],
        chapter: 'organization', hard: false,
        explanation: 'x4 and x8 DDR4 devices have four bank groups of four banks (16 banks). x16 devices have two groups of four banks (8 banks). The drill model uses two groups to keep the example small.',
        source: 'JESD79-4D sec 2.8' },

      { q: 'On a DDR4 column command, what does address pin A12/BC_n select when on-the-fly mode is enabled?',
        answers: [
          'BL8 when high, BC4 when low',
          'BL8 when low, BC4 when high',
          'The auto-precharge flag',
          'The bank group'
        ],
        chapter: 'commands', hard: false,
        explanation: 'A12/BC_n is the burst-chop control: high means BL8, low means BC4, valid only when MR0 A1:A0 = 01 (on-the-fly). A10 is the auto-precharge flag, and BG pins select bank groups.',
        source: 'JESD79-4D sec 4.3' },

      { q: 'During DDR4 initialization, in what order must the seven mode registers be loaded before ZQCL?',
        answers: [
          'MR3, MR6, MR5, MR4, MR2, MR1, MR0 (with DLL reset)',
          'MR0, MR1, MR2, MR3, MR4, MR5, MR6',
          'Any order as long as all are written',
          'MR1, MR0, MR2, MR3, MR4, MR5, MR6'
        ],
        chapter: 'init', hard: true,
        explanation: 'After CKE is high and tXPR has passed, the fixed MRS sequence is MR3, MR6, MR5, MR4, MR2, MR1, then MR0 with A8 = 1 to reset the DLL, followed by ZQCL and waits for tDLLK and tZQinit.',
        source: 'JESD79-4D sec 3.3.1' },

      { q: 'What does DDR4 gear-down mode change?',
        answers: [
          'Command/address timing runs in 1N (half-rate, default) or 2N (quarter-rate) mode',
          'It changes the data rate between BL8 and BC4',
          'It switches the DLL on and off',
          'It selects between per-bank and all-bank refresh'
        ],
        chapter: 'init', hard: false,
        explanation: 'Gear-down mode (MR3 A3) selects 1N or 2N command/address timing. 2N mode relaxes CA timing but requires even latency values. It has nothing to do with burst length, the DLL, or refresh granularity.',
        source: 'JESD79-4D sec 3.3.1' },

      { q: 'On a DDR4 RD or WR command, what is address bit A10 used for?',
        answers: [
          'The auto-precharge (AP) flag: A10 = 1 turns RD into RDA and WR into WRA',
          'BL8 versus BC4 selection',
          'The most-significant column bit',
          'Bank-group selection'
        ],
        chapter: 'commands', hard: false,
        explanation: 'A10 carries the auto-precharge flag on RD/WR commands. Column addressing uses A0-A9 (plus extra bits on some densities). BL8/BC4 is A12/BC_n, and bank groups are selected by BG pins.',
        source: 'JESD79-4D sec 4.1' },

      { q: 'When DDR4 ACT_n is low, what do the RAS_n/A16, CAS_n/A15, and WE_n/A14 pins carry?',
        answers: [
          'Row-address bits A16-A14; ACT_n reuses the command pins as address pins',
          'The bank-group and bank-select bits',
          'The auto-precharge and burst-chop flags',
          'The next column command'
        ],
        chapter: 'commands', hard: false,
        explanation: 'With ACT_n low the command pins serve as row-address bits A16-A14. The bank group and bank are carried on BG and BA pins; A10 and A12 are used on column commands.',
        source: 'JESD79-4D sec 4.1' },

      { q: 'Two consecutive column commands to the SAME bank group are spaced by...',
        answers: [
          'tCCDL, which is longer than tCCDS and prevents a single group from saturating the bus',
          'tCCDS, because same-group commands are the fast path',
          'tRRDL, the activate spacing',
          'tFAW, the four-activate window'
        ],
        chapter: 'timing', hard: true,
        explanation: 'Same-group column spacing is tCCDL (5-8 nCK by speed); cross-group spacing is tCCDS (4 nCK). tRRDL governs activates, not column commands, and tFAW is a rolling activate window.',
        source: 'JESD79-4D sec 4.24' },

      { q: 'A write followed by a read to a DIFFERENT bank group is governed by...',
        answers: [
          'tWTRS, which is speed-dependent and can be as small as 2 nCK',
          'tWTRL, the same-group write-to-read parameter',
          'tCCDS, the column-to-column spacing',
          'tRTW, the read-to-write turnaround'
        ],
        chapter: 'timing', hard: true,
        explanation: 'WR -> RD across bank groups uses tWTRS (max(2 nCK, 2.5 ns)); the actual nCK value depends on speed. Same-group WR -> RD uses the larger tWTRL. tRTW is RD -> WR, and tCCDS is same-direction column spacing.',
        source: 'JESD79-4D sec 4.24' },

      { q: 'Which formula gives the DDR4 read-to-write command spacing (book symbol tRTW)?',
        answers: [
          'RL - WL + BL/2 + 1 + RU(tWPRE)',
          'WL + BL/2 + RU(tWTR)',
          'BL/2 + 2 clocks',
          'tCCDS + tCCDL'
        ],
        chapter: 'timing', hard: true,
        explanation: 'JESD79-4D does not name tRTW, but the write-timing figures give the relation as RL - WL + BL/2 + 1 + RU(tWPRE). WL + BL/2 + RU(tWTR) is the write-to-read direction, and BL/2 + 2 is a simplified special case.',
        source: 'JESD79-4D sec 4.25' },

      { q: 'What is the purpose of the DDR4 ALERT_n pin?',
        answers: [
          'It reports write-CRC errors and CA parity errors as active-low alert pulses',
          'It carries the auto-precharge flag',
          'It is the chip-select for gear-down mode',
          'It provides the 2.5 V VPP supply'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'ALERT_n is an alert output. Write CRC mismatches and CA parity errors both drive it low; software reads MR5 and MPR page 1 to tell which error occurred. VPP is a separate 2.5 V supply pin.',
        source: 'JESD79-4D sec 4.16, 4.17' },

      { q: 'Which statement about DDR4 data-mask, DBI, and TDQS is correct?',
        answers: [
          'DM, write DBI, and read DBI are controlled by MR5; TDQS is enabled in MR1 and is mutually exclusive with DM/DBI on x8',
          'DM and write DBI can be enabled at the same time',
          'TDQS is available on all organizations and works with DBI',
          'Read DBI inverts bytes with fewer than four zeros'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'MR5 A10 enables DM, A11 enables write DBI, A12 enables read DBI; write DBI and DM are mutually exclusive. MR1 A11 enables TDQS on x8 only, and TDQS disables DM and DBI. Read DBI inverts when more than four bits are zero.',
        source: 'JESD79-4D sec 4.20' },

      { q: 'What happens when DDR4 write CRC is enabled?',
        answers: [
          'An 8-bit CRC is appended to the write burst, a mismatch is reported on ALERT_n, and effective write latency increases by one clock',
          'A CRC is appended to read data',
          'The burst length is forced to BC4',
          'CA parity is enabled automatically'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'Write CRC (MR5 A12) protects writes only. The controller appends an 8-bit CRC; the DRAM reports mismatches on ALERT_n and, when DM is also enabled, blocks bad writes. Enabling CRC adds one clock to write latency.',
        source: 'JESD79-4D sec 4.16' },

      { q: 'Which statement about DDR4 refresh is true?',
        answers: [
          'DDR4 has only all-bank refresh; FGR offers 1x, 2x, and 4x modes with matching tREFI and tRFC values',
          'DDR4 supports per-bank refresh like LPDDR3',
          'Refresh is optional above 85 C',
          'FGR 4x mode doubles the tREFI interval'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'JESD79-4D does not define per-bank refresh. Fine-granularity refresh (FGR) keeps all-bank refresh but lets the controller choose 1x (tREFI1 = 7.8 us), 2x (3.9 us), or 4x (1.95 us) with corresponding shorter tRFC values. Temperature above 85 C still requires halving the interval.',
        source: 'JESD79-4D sec 4.9' },

      { q: 'What is the DDR4 1x-mode average refresh interval at normal temperature, and how does it change above 85 C?',
        answers: [
          '7.8 us at 0-85 C, halved to 3.9 us above 85 C',
          '3.9 us at all temperatures',
          '7.8 us at all temperatures; only tRFC changes',
          '15.6 us at low temperature, 7.8 us above 85 C'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'In 1x FGR mode the average REF interval is 7.8 us at normal temperature and 3.9 us above 85 C. The same 2x scaling applies within 2x and 4x modes.',
        source: 'JESD79-4D sec 4.9' }
    ],

    commandDocs: [
      { cmd: 'ACT', name: 'Bank Activate',
        description: 'Opens row R in bank B selected by BG and BA. With ' +
                     'ACT_n low the RAS/A16, CAS/A15, WE/A14 pins carry ' +
                     'row-address bits. Spacing: tRCD to the first RD/WR, ' +
                     'tRRDS cross-group, tRRDL same-group, tFAW across any ' +
                     'four activates, tRC same bank.' },
      { cmd: 'PRE', name: 'Precharge (one bank or all banks)',
        description: 'Closes the open row and restores data. A10/AP = 0 ' +
                     'precharges the bank selected by BG/BA; A10/AP = 1 ' +
                     'precharges all banks. The bank is ready for a new ACT ' +
                     'after tRP.' },
      { cmd: 'RD', name: 'Read',
        description: 'Bursts BL8 or BC4 words from the open row starting at ' +
                     'the issued column; data appears RL = AL + CL + PL ' +
                     'clocks later. A10 = 0; A12/BC_n selects BL8/BC4 when ' +
                     'OTF is enabled. Cross-group spacing tCCDS; same-group ' +
                     'tCCDL; tRTW to a write.' },
      { cmd: 'RDA', name: 'Read with Auto-Precharge',
        description: 'RD with A10 = 1: the bank precharges itself once tRAS ' +
                     'and tRTP are met. Re-activation waits tRP from the ' +
                     'internal precharge and tRC from the old ACT.' },
      { cmd: 'WR', name: 'Write',
        description: 'Bursts BL8 or BC4 words into the open row; first data ' +
                     'is captured WL = AL + CWL + PL clocks after the command. ' +
                     'A10 = 0; A12/BC_n selects BL8/BC4 when OTF is enabled. ' +
                     'Write CRC or DM/DBI are mode-register options.' },
      { cmd: 'WRA', name: 'Write with Auto-Precharge',
        description: 'WR with A10 = 1: the bank precharges itself after write ' +
                     'recovery. Next ACT waits WL + BL/2 + nWR + tRP (and ' +
                     'tRC).' },
      { cmd: 'MRS', name: 'Mode Register Set',
        description: 'Writes one of MR0-MR6, selected by BG0, BA1, BA0. All ' +
                     'banks idle; tMRD between MRS commands, tMOD before any ' +
                     'non-MRS command. Carries CL, CWL, AL, BL, WR, DLL ' +
                     'reset/enable, gear-down, FGR, preamble, DBI, DM, TDQS, ' +
                     'CA parity, and VrefDQ training.' },
      { cmd: 'REF/REF1x/REF2x/REF4x', name: 'Refresh (all-bank, FGR modes)',
        description: 'One internal all-bank refresh step. All banks must be ' +
                     'precharged first; the device is busy for tRFC1/tRFC2/' +
                     'tRFC4 matching the FGR mode. Average rate tREFI1/' +
                     'tREFI2/tREFI4; up to 8 may be postponed (9 x tREFI ' +
                     'worst gap), up to 8 pulled in.' },
      { cmd: 'SRE/SRX', name: 'Self-Refresh Entry / Exit',
        description: 'Entry: REF encoding with CKE falling, all banks idle, ' +
                     'ODT off. Exit: CKE rises with stable clock, wait tXS ' +
                     'to non-DLL commands, tXSDLL = tDLLK to reads. At least ' +
                     'one REF before re-entering. MR4 A9 selects abort mode.' },
      { cmd: 'PDE/PDX', name: 'Power-Down Entry / Exit',
        description: 'CKE low with DES parks the device in precharge or ' +
                     'active power-down while keeping the DLL on. Exit to any ' +
                     'command: tXP. No refresh inside; stay bounded by ' +
                     'refresh requirements (9 x tREFI at best).' },
      { cmd: 'MPR', name: 'Multi-Purpose Register',
        description: 'Enter via MR3 A2 = 1 after precharging all banks. Page ' +
                     '0 outputs a training pattern, page 1 logs CA parity ' +
                     'errors, page 2 reflects mode-register readback, and ' +
                     'page 3 is vendor-specific. Only RD/RDA and MPR writes ' +
                     'are legal until MPR is exited.' },
      { cmd: 'NOP/DES', name: 'No Operation / Deselect',
        description: 'Bus fillers: NOP keeps CS_n low, DES raises CS_n. ' +
                     'Neither changes state. Required through mode-register, ' +
                     'self-refresh-exit, power-down, and gear-down windows.' },
      { cmd: 'ZQCL/ZQCS', name: 'ZQ Calibration Long / Short',
        description: 'ZQCL performs a full calibration of output driver and ' +
                     'ODT impedance against the external 240 ohm ZQ resistor; ' +
                     'required at init (tZQinit). ZQCS is a short periodic ' +
                     'update (tZQCS). All banks idle and tRP met.' },
      { cmd: 'ALERT#', name: 'Alert Output',
        description: 'Active-low output that pulses for write CRC errors and ' +
                     'CA parity errors. Software distinguishes the source by ' +
                     'reading MR5 status bits and MPR page 1.' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: [],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
