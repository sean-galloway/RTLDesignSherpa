// packs/hbm4.js -- HBM4 content pack (JESD270-4A).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/hbm4); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'hbm4',
    name: 'HBM4',
    jedec: {
      doc: 'JESD270-4A',
      note: 'High Bandwidth Memory 4. Most row timings are vendor-datasheet ' +
            'values; the standard defines symbol, unit and constraint.'
    },

    // Simplified drill topology: 2 bank groups of 4 banks, 8 rows, 8 cols,
    // 2 Stack IDs. Real parts: up to 32 channels x 2 pseudo channels,
    // 16-64 banks/PC, 1 KB pages, RA[13:0]/CA[4:0].
    topology: {
      hasBankGroups: true,
      groups: 2,
      banksPerGroup: 4,
      banks: 8,
      rows: 8,
      cols: 8,
      sids: 2
    },

    commands: ['ACT', 'PRE', 'RD', 'WR', 'RDA', 'WRA'],

    timingParams: [
      // --- chapter: core (row timings, per pseudo channel) -------------
      { symbol: 'tRCDRD', name: 'Row open to read data legal',
        definition: 'ACT to RD/RDA, same bank. Vendor-datasheet value.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|RDA', scope: 'same_bank' }] },
      { symbol: 'tRCDWR', name: 'Row open to write legal',
        definition: 'ACT to WR/WRA, same bank. Vendor-datasheet value.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'WR|WRA', scope: 'same_bank' }] },
      { symbol: 'tRAS', name: 'Minimum row-open time',
        definition: 'ACT to PRE (or internal precharge of RDA/WRA), same ' +
                    'bank. Max 9 x tREFI.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRP', name: 'Precharge to bank ready',
        definition: 'PRE to ACT (or REFpb), same bank. Vendor-datasheet value.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRC', name: 'Full activate cycle',
        definition: 'ACT to ACT, same bank; equals tRAS + tRP by construction.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRRDL', name: 'Activate spacing, same bank group',
        definition: 'ACT to ACT (or REFpb) when both banks are in one ' +
                    'group. Wider than tRRDS: same-group activates share ' +
                    'local resources.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_group' }] },
      { symbol: 'tRRDS', name: 'Activate spacing, different bank groups',
        definition: 'ACT to ACT (or REFpb) across bank groups.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_group' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'No more than 4 ACT (or REFpb) commands in any ' +
                    'tFAW-wide rolling window.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRTP', name: 'Read data to precharge',
        definition: 'RD/RDA to PRE, same bank. MR5 programs the nCK twin ' +
                    '(RTP >= RU(tRTP/tCK)).',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'Last write data to internal precharge legal. MR3 ' +
                    'programs WR >= RU(tWR/tCK); feeds tDAL on WRA.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tPPD', name: 'Precharge-to-precharge packing',
        definition: 'PRE to PRE, same pseudo channel. 2 nCK.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'PRE', scope: 'any' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCDL', name: 'Column command spacing, same bank group',
        definition: 'RD/WR to RD/WR, both banks in one group. ' +
                    'Max(4, 2.5 ns/tCK) nCK; 4 nCK at speed covers a BL8 ' +
                    'burst so same-group reads chain seamlessly.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'same_group' },
                    { from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tCCDS', name: 'Column command spacing, different bank groups',
        definition: 'RD/WR to RD/WR across groups. 2 nCK, so cross-group ' +
                    'commands interleave two per burst duration.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'diff_group' }] },
      { symbol: 'tCCDR', name: 'Read spacing across Stack IDs',
        definition: 'RD to RD crossing SIDs (8H and taller only). Replaces ' +
                    'tCCDS for seamless cross-SID reads; vendor value in ' +
                    'the tCCDS+1..tCCDS+2 nCK range. Reads only - writes ' +
                    'crossing SIDs use plain tCCDS.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'diff_sid' }] },
      { symbol: 'tWTRL', name: 'Write to read, same bank group',
        definition: 'Internal write-to-read, banks in one group (same ' +
                    'bank included). Command-bus form: WR -> RD = ' +
                    'WL + 2 + tWTRL.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'same_group' },
                    { from: 'WR|WRA', to: 'RD|RDA', scope: 'same_bank' }] },
      { symbol: 'tWTRS', name: 'Write to read, different bank groups',
        definition: 'Internal write-to-read across groups. Command-bus ' +
                    'form: WR -> RD = WL + 2 + tWTRS.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'diff_group' }] },
      { symbol: 'tRTW', name: 'Read-to-write bus turnaround',
        definition: 'Not an array limit: the shared DQ/DBI/ECC pins ' +
                    'changing ownership. Controller-computed: ' +
                    '(RL + BL/4 - WL + 0.5) x tCK + tWDQS2DQ_O(max) - ' +
                    'tWDQS2DQ_I(min), rounded up.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },

      // --- chapter: refresh (reference panel; the drill engine does ----
      // --- not emit REF commands, so these never match a question) -----
      { symbol: 'tREFI', name: 'Average refresh interval',
        definition: 'REFab to REFab. 3.9 us max; 0.5x / 0.25x past ' +
                    'temperature trip points. Up to 8 REFab may be ' +
                    'postponed (9 x tREFI absolute bound).',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFCab', name: 'All-bank refresh cycle',
        definition: 'REFab to next access. 360-530 ns by die density and ' +
                    'stack height. All banks precharged first.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'any' }] },
      { symbol: 'tRFCpb', name: 'Per-bank refresh cycle, same bank',
        definition: 'REFpb to next access of that bank. 240 ns (24 Gb/die) ' +
                    '/ 280 ns (32 Gb/die).',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'same_bank' }] },
      { symbol: 'tRREFD', name: 'Per-bank refresh spacing, different banks',
        definition: 'REFpb to REFpb (or ACT) of a different bank. ' +
                    'MAX(3 x tCK, 8 ns).',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF|ACT', scope: 'diff_bank' }] }
    ],

    questionBank: [
      { q: 'An HBM4 channel splits into two pseudo channels. What does each pseudo channel own?',
        answers: [
          'An independent bank set with a 1 KB page size and a 256-bit prefetch per access',
          'Half of the channel row bus and its own mode registers',
          'A private copy of the channel clock and CATTRIP',
          'One quarter of the stack channels'
        ],
        chapter: 'organization', hard: false,
        explanation: 'Each pseudo channel (PC0/PC1, 32 DQ each) has an independent bank set, 1 KB page and 256-bit prefetch; a request to one PC can never reach the other\'s data. The two PCs SHARE the channel row bus, column bus, CK and mode registers.',
        source: 'JESD270-4A sec 3.1.2' },

      { q: 'Why can an HBM4 channel issue an activate in the same cycle as a read?',
        answers: [
          'Row commands (ACT/PRE/REF...) travel on the R[9:0] row bus while column commands (RD/WR/MRS) travel on the separate C[7:0] column bus',
          'ACT is always compressed into the read command address bits',
          'Pseudo channel 0 handles reads while pseudo channel 1 handles activates',
          'The base logic die serializes and re-issues both commands'
        ],
        chapter: 'organization', hard: false,
        explanation: 'Each channel has two semi-independent command buses: the row bus R[9:0] (ACT, PRE, REF, PDE/SRE...) and the column bus C[7:0] (RD, RDA, WR, WRA, MRS). Separate buses mean a row command and a column command can land in the same cycle.',
        source: 'JESD270-4A sec 3.1.3' },

      { q: 'On an 8-high (8H) HBM4 stack, how is the per-pseudo-channel bank address formed?',
        answers: [
          '{SID[0], BA[3:0]} - one Stack ID bit plus four bank bits, 32 banks per pseudo channel',
          'BA[4:0] - five flat bank bits, no Stack ID',
          '{BA[3:0], SID[0]} - SID is the least significant bit',
          'BA[3:0] only; SID exists on 16H parts only'
        ],
        chapter: 'organization', hard: true,
        explanation: '4H parts use BA[3:0] (16 banks/PC, no SID). 8H grows the field to {SID[0], BA[3:0]} (32 banks/PC); 12H/16H use {SID[1:0], BA[3:0]} (48/64 banks/PC, SID[1:0]=11 invalid).',
        source: 'JESD270-4A sec 3.2 Table 4' },

      { q: 'Which commands actually use the SID bits?',
        answers: [
          'ACT, PREpb, REFpb, RFMpb, RD and WR - all other commands ignore SID',
          'Every command, because SID is part of the channel address',
          'Only RD and WR, because SID selects the data DWORD',
          'Only ACT, because SID selects the die at row-open time'
        ],
        chapter: 'organization', hard: true,
        explanation: 'SID bits behave as extra bank-address bits on ACT, PREpb, REFpb, RFMpb, RD and WR only. Commands not in that list do not use SID.',
        source: 'JESD270-4A sec 3.2 Table 4 notes' },

      { q: 'ACT to ACT in the SAME bank group is governed by...',
        answers: [
          'tRRDL - wider than tRRDS because same-group activates share local resources',
          'tRRDS - cross-group activates are always slower',
          'tFAW - the rolling window replaces per-pair spacing inside a group',
          'tRC - the same-bank cycle applies to any two activates in a group'
        ],
        chapter: 'timing', hard: false,
        explanation: 'Same-group ACT spacing is tRRDL, different-group is tRRDS. In practice tRRDL > tRRDS: banks in one group share local resources and must be spaced wider. tRC is same-BANK only; tFAW is a separate rolling-window limit on top of both.',
        source: 'JESD270-4A Table 6' },

      { q: 'tFAW limits which of the following?',
        answers: [
          'No more than 4 ACT or REFpb commands in any rolling tFAW-wide window',
          'The number of banks that may be open at once',
          'Activate spacing inside one bank group',
          'The time a row may stay open before refresh'
        ],
        chapter: 'timing', hard: false,
        explanation: 'tFAW is a rolling current limit: with RU(tFAW/tCK) = 25 clocks and an ACT at T0, at most three more ACTs may land in T1..T24. Per-bank REFpb commands count against the same window.',
        source: 'JESD270-4A sec 10, Table 108' },

      { q: 'Two consecutive READs to different Stack IDs are spaced by...',
        answers: [
          'tCCDR, which replaces tCCDS for cross-SID reads on 8H and taller parts',
          'tCCDS, the same as any cross-group read pair',
          'tRTW, because crossing SIDs reverses the bus',
          'tRREFD, because SID crossings count as refreshes'
        ],
        chapter: 'timing', hard: true,
        explanation: 'tCCDR ("RD SID A to RD SID B") exists only on parts with SIDs and replaces tCCDS for seamless consecutive reads across SIDs; its minimum is vendor-specific, roughly tCCDS+1..tCCDS+2 nCK. It applies to reads only - writes crossing SIDs use plain tCCDS.',
        source: 'JESD270-4A Table 108 note 17, Table 6 note 2' },

      { q: 'Why is tCCDL (4 nCK at high speed) the "seamless" same-group read spacing?',
        answers: [
          'A BL8 burst occupies exactly 4 CK of DQ data, so a read every 4 clocks keeps the bus full',
          'The row bus takes 4 cycles to be reused inside a group',
          'tCCDL counts pseudo-channel arbitration overhead',
          '4 nCK is the DLL lock granularity'
        ],
        chapter: 'timing', hard: true,
        explanation: 'BL8 occupies 4 CK of data on the bus. tCCDL = Max(4, 2.5 ns/tCK) nCK means a same-group read every 4 clocks chains bursts back-to-back with no bubble; tCCDS = 2 nCK lets cross-group commands interleave two per burst duration.',
        source: 'JESD270-4A sec 6.3.3' },

      { q: 'tRTW on HBM4 is best described as...',
        answers: [
          'A controller-computed bus-ownership delay: (RL + BL/4 - WL + 0.5) x tCK plus strobe offset terms',
          'A DRAM array limit between read data and the next write command',
          'A fixed 2 nCK bus turnaround like tCCDS',
          'The read preamble length of DQS'
        ],
        chapter: 'timing', hard: true,
        explanation: 'tRTW is NOT a DRAM array limit; it is the time the shared bidirectional DQ/DBI/ECC pins need to change ownership. Because RL and WL are mode-register values, tRTW is system-derived: two controllers with different latency programming compute different tRTW for the same DRAM.',
        source: 'JESD270-4A sec 6.3.3' },

      { q: 'What is the maximum average refresh interval tREFI, and what happens at high temperature?',
        answers: [
          '3.9 us; the host must shorten it to 0.5x then 0.25x past vendor temperature trip points',
          '7.8 us; it doubles above 85 C',
          '3.9 us; it never changes, only tRFC changes',
          '32 ms per refresh window like LPDDR2'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'tREFI is 3.9 us max. Past vendor trip points the host shortens it (0.5x, 0.25x); CHANNEL_TEMPERATURE reads the per-channel sensors. Up to 8 REFab may be postponed, giving a 9 x tREFI absolute bound.',
        source: 'JESD270-4A Table 38' },

      { q: 'Under per-bank refresh (REFpb), which statement is correct?',
        answers: [
          'REFpb counts against tFAW like an ACT, and every bank of an SID must be refreshed before any bank of that SID is refreshed a second time',
          'REFpb is free: it consumes no activate-related budget at all',
          'REFpb to the same bank must wait tRREFD',
          'Banks of an SID must be refreshed strictly in ascending order'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'REFpb counts as an activation for tFAW. tRREFD spaces REFpb to a DIFFERENT bank (same bank is tRFCpb). Within an SID banks can be refreshed in any order, but all of them must be covered before any repeat.',
        source: 'JESD270-4A sec 6.3.4.2' },

      { q: 'A part flags RFM=1 in DEVICE_ID. What must the controller do?',
        answers: [
          'Keep a per-bank rolling activate count (RAA) and issue RFMab/RFMpb when the count reaches the RAAIMT threshold',
          'Halve tREFI permanently',
          'Alternate every activate between the two pseudo channels',
          'Nothing - RFM is a DRAM-internal background scrub'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'Refresh management is controller work: per-bank RAA counters, RFMab (all banks) or RFMpb (one bank) at RAAIMT, RAAMMT as the hard maximum, adaptive threshold sets via MR8. DRFM can direct the refresh at a row captured by a flagged ACT.',
        source: 'JESD270-4A sec 6.3.2.5' },

      { q: 'Which data-integrity feature is MANDATORY on HBM4?',
        answers: [
          'Symbol-based on-die ECC: a 272-bit data-word of 256 data bits plus 16 metadata bits on the ECC pins',
          'DBIac on every DWORD',
          'CA parity with write-leveling recovery',
          'CRC on read data'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'HBM4 mandates symbol-based on-die ECC (272b word = 256b data + 16b MD on the ECC pins), with SEV-pin severity reporting (NE/CEs/CEm/UE) and ECS scrub. DBIac and parity features exist but DBI is mode-register selectable.',
        source: 'JESD270-4A sec 4 (book ch05/02_dbi_ecc.md)' },

      { q: 'Where do the nCK-programmed twins of tRAS, tWR and tRTP live, and what constraint ties them to the analog values?',
        answers: [
          'MR4 (RAS), MR3 (WR), MR5 (RTP); each programmed value must be >= RU(t_analog/tCK)',
          'MR0 for all three; they must equal the analog values exactly',
          'The vendor base die fuses them at test; they are not programmable',
          'MR1/MR2/MR3; they may be programmed below the analog values for speed'
        ],
        chapter: 'init', hard: true,
        explanation: 'The DRAM uses the MR-programmed nCK values for auto precharge, so they must round UP from the analog minimums. Parts without nCK programming ignore the MR fields and use the analog values.',
        source: 'JESD270-4A sec 10, Tables 36, 108' },

      { q: 'tRC, the same-bank activate cycle, equals...',
        answers: [
          'tRAS + tRP by construction: the row must be open long enough, then the bank must recover from precharge',
          'tRCD + tRTP + tRP: the read path defines the cycle',
          '4 x tRRDL: four same-group activates bound the cycle',
          'A vendor value unrelated to other parameters'
        ],
        chapter: 'timing', hard: false,
        explanation: 'tRC bounds ACT-to-ACT on one bank and must cover tRAS (earliest legal PRE) plus tRP (precharge to ready). The canonical cycle is ACT -> (tRAS) -> PRE -> (tRP) -> ACT.',
        source: 'JESD270-4A sec 10, Table 108' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: ['sid', 'cross_group'],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
