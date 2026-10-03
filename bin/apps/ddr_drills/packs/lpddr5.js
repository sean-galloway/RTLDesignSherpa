// packs/lpddr5.js -- LPDDR5 content pack (JESD209-5C).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/lpddr5); every question cites the spec
// section or table the book cites. Dual-environment header: same bytes run
// as a browser <script> tag and under node require() in the test harness.
//
// LPDDR5 is a FLAT topology in the drill model: no bank groups, no Stack IDs.
// Scopes used: same_bank / diff_bank / any. The real die contains two
// independent channels and three selectable bank organizations (BG, 8B, 16B);
// this pack models one channel in 8-bank mode.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'lpddr5',
    name: 'LPDDR5',
    jedec: {
      doc: 'JESD209-5C',
      note: 'Low Power DDR5. Dual-channel die, forwarded WCK clocking, ' +
            'selectable BG/8B/16B organization, BL16/BL32, link ECC, ' +
            'Refresh Management (RFM), three Frequency Set Points (FSP).'
    },

    // Simplified drill topology: 8 flat banks, 8 rows, 8 cols. Real parts are
    // dual-channel dies and the bank organization is selectable via MR3
    // OP[4:3] (BG = 4 groups x 4 banks, 8B = flat 8 banks, 16B = flat 16
    // banks). The drill model uses 8-bank mode with BL32.
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
      { symbol: 'tRCD', name: 'RAS-to-CAS delay',
        definition: 'ACT to RD/WR/RDA/WRA, same bank. Row open to first ' +
                    'column command. max(18 ns, 2 nCK) in x16 mode with DVFSC ' +
                    'and write link ECC disabled.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tRPpb', name: 'Precharge time, one bank',
        definition: 'PRE (single bank) to ACT of that bank. max(18 ns, 2 nCK) ' +
                    'in x16 mode.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRPab', name: 'Precharge time, all banks',
        definition: 'PRE-all to ACT of any bank. max(21 ns, 2 nCK) in x16 ' +
                    'mode; longer than tRPpb. Panel only - the drill model\'s ' +
                    'PRE is per-bank.',
        chapter: 'core',
        appliesTo: [{ from: 'PREA', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRAS', name: 'Minimum row-active time',
        definition: 'ACT to PRE, same bank. min = max(42 ns, 3 nCK); max = ' +
                    'min(9 x RefreshRate x tREFI, 70.2 us).',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRC', name: 'Row cycle',
        definition: 'ACT to ACT, same bank: tRAS + tRPpb after a per-bank ' +
                    'PRE, or tRAS + tRPab after a PRE-all.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRRD', name: 'Activate spacing, different banks',
        definition: 'ACT to ACT, different banks. max(10 ns, 2 nCK) in 8B ' +
                    'mode; relaxed to max(5 ns, 2 nCK) in BG/16B mode. A ' +
                    'REFpb counts as an activation for tFAW.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_bank' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'At most 4 ACTs (or REFpb operations) in any rolling ' +
                    'window. 40 ns in 8B mode; 20 ns in BG/16B mode.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'WR/WRA to PRE, same bank. max(34 ns, 3 nCK) for x16 ' +
                    'with write link ECC off. The nWR field in MR2 carries the ' +
                    'programmed clocks for auto-precharge.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRBTP', name: 'Read burst end to precharge',
        definition: 'RD/RDA to PRE, same bank. The programmed nRBTP value ' +
                    'from MR2 OP[3:0] determines the internal precharge start ' +
                    'after a read with auto-precharge. For the drill RL code ' +
                    '(0101B, CKR 4:1) nRBTP = 2 nCK.',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tPPD', name: 'Precharge-to-precharge spacing',
        definition: 'PRE to PRE, same channel. 2 nCK minimum between ' +
                    'back-to-back PRE commands; does not apply to ' +
                    'auto-precharges.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'PRE', scope: 'any' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCD', name: 'Column-to-column spacing',
        definition: 'Same-direction column commands, any banks: 4 nCK for ' +
                    'BL32 at CKR 4:1 (8 beats per CK, BL/n = 4). BG/16B modes ' +
                    'can also select BL16, where tCCD would be 2 nCK at CKR ' +
                    '4:1.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'any' },
                    { from: 'WR|WRA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tWTR', name: 'Write-to-read delay',
        definition: 'End of write burst data to RD. max(12 ns, 4 nCK) for ' +
                    'x16 in 8B/16B mode. BG mode splits this into tWTR_S ' +
                    '(max(6.25 ns, 4 nCK), different BG) and tWTR_L ' +
                    '(max(12 ns, 4 nCK), same BG). Command gap from WR to RD ' +
                    '= WL + BL/n + RU(tWTR/tCK).',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'any' }] },
      { symbol: 'tRTW', name: 'Read-to-write turnaround',
        definition: 'Named in JESD209-5C. For the simple case (RDQS_t as ' +
                    'input disabled, NT-ODT/ODT disabled, CKR 4:1) the command ' +
                    'gap is RL + BL/n + RU(tWCK2DQO(MAX)/tCK) - WL. The value ' +
                    'varies with bank organization, WCK:CK ratio, DQ ODT, ' +
                    'NT-ODT, read DQS settings, write link ECC, and training ' +
                    'modes.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },

      // --- chapter: init (reference panel; MRW/MRR are not engine cmds) -
      { symbol: 'tMRW', name: 'Mode-register write command period',
        definition: 'MRW to MRW. max(10 ns, 5 nCK). Panel only - the drill ' +
                    'engine does not emit MRW.',
        chapter: 'init',
        appliesTo: [{ from: 'MRW', to: 'MRW', scope: 'any' }] },
      { symbol: 'tMRR', name: 'Mode-register read command period',
        definition: 'MRR to MRR. 4 nCK at CKR 4:1, 8 nCK at CKR 2:1; only ' +
                    'DES is allowed during tMRR. Panel only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRR', to: 'MRR', scope: 'any' }] },
      { symbol: 'tMRD', name: 'Mode-register command spacing',
        definition: 'MRW to the next valid non-MRW command. max(14 ns, 5 ' +
                    'nCK). Panel only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRW', to: '*', scope: 'any' }] },

      // --- chapter: refresh (reference panel; REF/SRX are engine-only) -
      { symbol: 'tREFI', name: 'Average refresh interval',
        definition: 'Average REFab interval: 3.906 us at 1x rate (8192 ' +
                    'REFab per 32 ms tREFW). Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tREFW', name: 'Refresh window',
        definition: 'Rolling window in which 8192 REFab commands must be ' +
                    'distributed: 32 ms at 1x rate. Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFCab', name: 'All-bank refresh cycle',
        definition: 'REFab to next command, device busy. 180 ns for 4 Gb ' +
                    '(72 nCK at 400 MHz); scales with density. Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'any' }] },
      { symbol: 'tRFCpb', name: 'Per-bank refresh cycle',
        definition: 'REFpb to ACT of the same bank or the next REFpb. 90 ns ' +
                    'for 4 Gb (36 nCK at 400 MHz); scales with density. Panel ' +
                    'only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REFpb', to: 'ACT|REFpb', scope: 'same_bank' }] },
      { symbol: 'tXSR', name: 'Self-refresh exit to command',
        definition: 'SRX to any valid command. tRFCab + max(7.5 ns, 2 nCK). ' +
                    'WCK2CK sync must be re-established before the next data ' +
                    'burst. Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] },
      { symbol: 'tXP', name: 'Power-down exit',
        definition: 'PDX to any valid command. max(7 ns, 3 nCK). Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] }
    ],

    questionBank: [
      { q: 'What is the LPDDR5 prefetch and burst behavior in 8-bank mode?',
        answers: [
          '32n prefetch with BL32 as the only supported burst length',
          '16n prefetch with BL16 and BL32 selectable',
          '16n prefetch with BL16 as the only supported burst length',
          '32n prefetch with BL16 and BL32 selectable'
        ],
        chapter: 'organization', hard: false,
        explanation: '8-bank mode uses a 32n prefetch and supports BL32 only. ' +
                     'BG and 16B modes use a 16n prefetch and allow BL16 or BL32.',
        source: 'JESD209-5C sec 2.2.3' },

      { q: 'How many bank organizations can LPDDR5 select through MR3 OP[4:3]?',
        answers: [
          'Three: 4 bank groups x 4 banks, flat 8 banks, or flat 16 banks',
          'Two: flat 8 banks or flat 16 banks',
          'Four: 4 BG x 4 banks, 2 BG x 4 banks, 8 banks, and 16 banks',
          'One: flat 16 banks only'
        ],
        chapter: 'organization', hard: false,
        explanation: 'MR3 OP[4:3] selects 00B = BG (4 groups x 4 banks), 01B = ' +
                     '8B, or 10B = 16B. The default at reset is 16B mode.',
        source: 'JESD209-5C sec 2.2.3, sec 6.3 (MR3), Table 68' },

      { q: 'What is the default LPDDR5 bank organization at power-up, and what ' +
           'is the default WCK:CK ratio?',
        answers: [
          '16-bank mode and WCK:CK = 2:1',
          '8-bank mode and WCK:CK = 4:1',
          '16-bank mode and WCK:CK = 4:1',
          'Bank-group mode and WCK:CK = 2:1'
        ],
        chapter: 'organization', hard: true,
        explanation: 'The power-up default is MR3 OP[4:3] = 10B (16-bank mode) ' +
                     'and MR18 OP[7] = 1B (WCK:CK 2:1). The drill model switches ' +
                     'to 8-bank mode and 4:1 for its examples.',
        source: 'JESD209-5C sec 2.2.3, sec 6.3 (MR3/MR18), Table 68, Table 101' },

      { q: 'How is a full LPDDR5 device reset performed?',
        answers: [
          'By driving the dedicated RESET_n pin low for at least tINIT1 after ' +
          'supplies are stable',
          'By an MRW to a reset register',
          'By holding CKE low for 2 ms with no clock',
          'By issuing PREA followed by REFab'
        ],
        chapter: 'init', hard: false,
        explanation: 'LPDDR5 has a dedicated RESET_n pin. For reset with stable ' +
                     'power, drive RESET_n low for at least tPW_RESET (100 ns); ' +
                     'after power-up, hold it low for at least tINIT1 (200 us). ' +
                     'There is no MRW full reset.',
        source: 'JESD209-5C sec 4.1, Table 21' },

      { q: 'Which MR bit selects the active WCK:CK ratio, and what are the ' +
           'two choices?',
        answers: [
          'MR18 OP[7]: 4:1 (0B) or 2:1 (1B)',
          'MR16 OP[3:2]: 4:1 or 2:1',
          'MR18 OP[7]: 2:1 (0B) or 4:1 (1B)',
          'MR3 OP[5]: Set A or Set B'
        ],
        chapter: 'init', hard: false,
        explanation: 'MR18 OP[7] sets the WCK:CK ratio: 0B = 4:1, 1B = 2:1. ' +
                     'MR16 selects frequency-set points and MR3 OP[5] selects ' +
                     'WL Set A/B.',
        source: 'JESD209-5C sec 2.2.3, sec 6.3 (MR18), Table 101' },

      { q: 'Which MR register fields select the active frequency-set point and ' +
           'the register set targeted by MRW/MRR?',
        answers: [
          'MR16 OP[3:2] = FSP-OP (active set), OP[1:0] = FSP-WR (write target)',
          'MR16 OP[1:0] = FSP-OP, OP[3:2] = FSP-WR',
          'MR18 OP[7:6] = FSP-OP, OP[5:4] = FSP-WR',
          'MR3 OP[7:6] = FSP-OP, OP[5:4] = FSP-WR'
        ],
        chapter: 'init', hard: true,
        explanation: 'MR16 OP[3:2] selects which of the three FSP copies is ' +
                     'active (FSP-OP), while OP[1:0] selects which copy an MRW ' +
                     'or MRR accesses (FSP-WR). MR18 controls WCK, not FSP.',
        source: 'JESD209-5C sec 6.3 (MR16), Table 97' },

      { q: 'Which LPDDR5 command carries byte-mask information on the DMI pin?',
        answers: [
          'Masked Write (MWR), and it is BL16 only',
          'A normal Write with the DM pin held high',
          'MPC Write FIFO',
          'MRW to the data-mask register'
        ],
        chapter: 'commands', hard: false,
        explanation: 'LPDDR5 has no dedicated DM pin. Masking uses the MWR ' +
                     'command with DMI high per byte lane to mask that byte for ' +
                     'the whole burst. MWR is BL16 only.',
        source: 'JESD209-5C sec 7.4.6' },

      { q: 'How many CK cycles does an LPDDR5 ACT command occupy?',
        answers: [
          'Two consecutive one-cycle commands: ACT-1 followed by ACT-2',
          'One CK cycle, like RD/WR',
          'Four CK cycles',
          'ACT-1, then a CAS, then ACT-2'
        ],
        chapter: 'commands', hard: false,
        explanation: 'ACT is a two-cycle command: ACT-1 immediately followed by ' +
                     'ACT-2. The row address is split across both cycles. A gap ' +
                     'of up to 8 CK cycles is allowed between them with only ' +
                     'certain commands inserted.',
        source: 'JESD209-5C sec 7.3, Table 201' },

      { q: 'What is the LPDDR5 tRTW formula in the simplest case (RDQS_t as ' +
           'input disabled, ODT and NT-ODT disabled, CKR 4:1)?',
        answers: [
          'RL + BL/n + RU(tWCK2DQO(MAX)/tCK) - WL',
          'WL + BL/n + RU(tWTR/tCK)',
          'BL/n + 2 clocks',
          'tCCD + tWTR'
        ],
        chapter: 'timing', hard: true,
        explanation: 'JESD209-5C names tRTW and gives RL + BL/n + ' +
                     'RU(tWCK2DQO(MAX)/tCK) - WL for the simple case. The other ' +
                     'formulas are write-to-read (WL + BL/n + tWTR), a generic ' +
                     'burst spacing, or a same-direction/direction-change mix-up.',
        source: 'JESD209-5C sec 8.2.1, Table 349' },

      { q: 'In the drill configuration (CK = 400 MHz, BL32 at CKR 4:1, RL=12, ' +
           'WL=5), what is the total command gap from a WR to the next RD?',
        answers: [
          '14 nCK (WL + BL/n + RU(tWTR/tCK) = 5 + 4 + 5)',
          '12 nCK (the tRTW value)',
          '9 nCK (WL + BL/n + tCCD)',
          '5 nCK (just tWTR)'
        ],
        chapter: 'timing', hard: true,
        explanation: 'tWTR is measured from the CK edge that satisfies WL + ' +
                     'BL/n after the write command. With tWTR = max(12 ns, 4 ' +
                     'nCK) = 5 nCK, the total WR->RD gap is 5 + 4 + 5 = 14 nCK. ' +
                     'tRTW is the read-to-write direction.',
        source: 'JESD209-5C sec 7.4.7.4, Table 339, Table 383' },

      { q: 'What is the LPDDR5 column-to-column spacing tCCD for BL32 at ' +
           'WCK:CK 4:1 in 8-bank mode?',
        answers: [
          '4 nCK',
          '2 nCK',
          '8 nCK',
          '16 nCK'
        ],
        chapter: 'timing', hard: false,
        explanation: 'At CKR 4:1 the bus transfers 8 beats per CK, so BL32 ' +
                     '(32 beats) spans 4 CK. tCCD is therefore 4 nCK for ' +
                     'same-direction column commands.',
        source: 'JESD209-5C Table 339' },

      { q: 'Which two LPDDR5 features are mutually exclusive because both need ' +
           'the DMI pin during read bursts?',
        answers: [
          'Read DBI and read link ECC',
          'Write DBI and write link ECC',
          'Read DBI and masked write',
          'Write data copy and read link ECC'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'Read DBI uses DMI to tell the controller whether each ' +
                     'byte was inverted. Read link ECC uses DMI to carry ECC ' +
                     'check bits. Because both drive DMI during reads, only one ' +
                     'may be enabled.',
        source: 'JESD209-5C sec 7.4.10' },

      { q: 'Which statement about LPDDR5 data protection is correct?',
        answers: [
          'Link ECC is the only interface protection; there is no on-die ECC ' +
          'and no data-path CRC',
          'Write CRC is mandatory and reported on ALERT_n',
          'CA parity is optional and logged in MPR page 1',
          'On-die ECC is required for all densities'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'LPDDR5 protects only the DQ/DMI/RDQS_t interface with ' +
                     'optional read and write link ECC. It has no on-die ECC, ' +
                     'no write CRC, and no CA parity.',
        source: 'JESD209-5C sec 7.4.10, sec 7.4.9' },

      { q: 'What is the LPDDR5 average all-bank refresh interval at 1x rate?',
        answers: [
          '3.906 us, because 8192 REFab commands must fit in a 32 ms tREFW',
          '7.8 us, the same as DDR4',
          '1.953 us, twice the LPDDR4 rate',
          '15.6 us, half the LPDDR3 rate'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'LPDDR5 requires 8192 REFab commands per 32 ms window, so ' +
                     'the average interval is 32 ms / 8192 = 3.906 us. This is ' +
                     'the same count as LPDDR4.',
        source: 'JESD209-5C Table 241' },

      { q: 'What triggers the need for a Refresh Management (RFM) command in ' +
           'LPDDR5?',
        answers: [
          'A per-bank rolling accumulated ACT count reaching the RAAIMT ' +
          'threshold reported in MR27 OP[5:1]',
          'tREFI expiring',
          'A temperature-compensated refresh multiplier change',
          'A write link ECC error'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'RFM is driven by the RAA counter, which increments per ' +
                     'ACTIVATE per bank. When RAA reaches RAAIMT the DRAM sets ' +
                     'MR27 OP[0]=1 and the controller issues RFMab/RFMpb. It is ' +
                     'independent of tREFI and refresh multipliers.',
        source: 'JESD209-5C sec 7.5.4, sec 7.7.5' }
    ],

    commandDocs: [
      { cmd: 'ACT', name: 'Activate',
        description: 'Opens row R in bank B. Issued as ACT-1 immediately ' +
                     'followed by ACT-2 on the 7-bit CA bus; the row address is ' +
                     'split across both cycles and the bank address is carried ' +
                     'in ACT-1. Spacing: tRCD to the first RD/WR, tRRD to the ' +
                     'next ACT, tFAW across any four, tRC same bank.' },
      { cmd: 'RD', name: 'Read',
        description: 'Starts a BL16 or BL32 read burst from the open row. In ' +
                     '8-bank mode the command is simply RD; in BG/16B mode the ' +
                     'BL bit selects BL16/BL32. Data returns RL CK cycles after ' +
                     'the command plus WCK2CK and WCK2DQO timing. ' +
                     'Same-direction spacing tCCD = 4 clocks (BL32 at CKR 4:1); ' +
                     'tRTW to a write.' },
      { cmd: 'WR', name: 'Write',
        description: 'Starts a BL16 or BL32 write burst. First data is ' +
                     'captured WL CK cycles after the command, with WCK aligned ' +
                     'to the data. Use Masked Write when any beat must be ' +
                     'masked. Same-direction spacing tCCD; tWTR to a read.' },
      { cmd: 'RDA', name: 'Read with Auto-Precharge',
        description: 'RD with AP = 1: the bank precharges itself once tRAS ' +
                     'and the programmed nRBTP are met. Re-activation waits ' +
                     'tRPpb and tRC from the old ACT.' },
      { cmd: 'WRA', name: 'Write with Auto-Precharge',
        description: 'WR with AP = 1: the bank precharges itself after write ' +
                     'recovery (WL + BL/n + 1 + nWR past the command). ' +
                     'Re-activation waits tRPpb and tRC.' },
      { cmd: 'PRE', name: 'Precharge',
        description: 'Closes the open row of one bank or all banks. AB = 1 ' +
                     'precharges all banks (tRPab); AB = 0 precharges the bank ' +
                     'selected by BA (tRPpb). Must not violate tRAS, tRBTP, or ' +
                     'tWR.' },
      { cmd: 'MRR', name: 'Mode Register Read',
        description: 'Reads one of the mode registers back onto DQ[7:0] ' +
                     'during a BL16 burst. Only DES is allowed during the tMRR ' +
                     'window.' },
      { cmd: 'MRW', name: 'Mode Register Write',
        description: 'Two-cycle command (MRW-1 + MRW-2) carrying 7-bit ' +
                     'register address and 8-bit operand. All banks must be ' +
                     'idle; tMRW between MRWs, tMRD to the next non-MRW ' +
                     'command. Carries BL, RL/WL, nWR, DBI, ODT, FSP, and ' +
                     'training controls.' },
      { cmd: 'MPC', name: 'Multi-Purpose Command',
        description: 'Provides NOP (OP6 = 0) and training/calibration ' +
                     'operations. Write FIFO, Read FIFO, and Read DQ ' +
                     'Calibration may require CAS immediately after MPC. ZQCal ' +
                     'Start/Latch and WCK interval oscillator control are also ' +
                     'accessed through MPC.' },
      { cmd: 'MWR', name: 'Masked Write',
        description: 'BL16 write command that uses the DMI pin to mask byte ' +
                     'lanes. DMI high masks the corresponding byte for the ' +
                     'entire burst. Two masked writes to the same bank must be ' +
                     'separated by tCCDMW.' },
      { cmd: 'REFab/REFpb/RFM', name: 'Refresh All / Per Bank / Management',
        description: 'REFab refreshes every bank and needs all banks idle; ' +
                     'wait tRFCab. REFpb refreshes the addressed bank; wait ' +
                     'tRFCpb for that bank. Eight REFpb operations replace one ' +
                     'REFab of coverage. RFMab/RFMpb are issued when MR27 ' +
                     'OP[0]=1 to decrement the rolling accumulated ACT count.' },
      { cmd: 'SRE/SRX/DSM', name: 'Self-Refresh Entry / Exit / Deep Sleep',
        description: 'Entry: SRE encoding with all banks idle and CKE falling. ' +
                     'Deep sleep is requested by setting DSM=1 in SRE (mutually ' +
                     'exclusive with PD). Exit: CKE rises; wait tXSR to any ' +
                     'valid command and re-establish WCK2CK sync before the ' +
                     'next data burst. At least one extra refresh is required ' +
                     'before re-entering self refresh.' },
      { cmd: 'PDE/PDX', name: 'Power-Down Entry / Exit',
        description: 'CKE low parks the channel in active or idle power-down. ' +
                     'No refresh occurs, so dwell time is bounded by the ' +
                     'refresh schedule. Exit: CKE rises; first valid command ' +
                     'after tXP.' },
      { cmd: 'NOP/DES', name: 'No Operation / Deselect',
        description: 'NOP (CS high, CA all low) and DES (CS low) hold the bus ' +
                     'idle for one cycle without aborting in-flight ' +
                     'operations. MPC with OP6 = 0 acts as a two-cycle NOP. ' +
                     'Used to fill forced gaps such as tRRD, tCCD, tMRW, and ' +
                     'turnaround bubbles.' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: [],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
