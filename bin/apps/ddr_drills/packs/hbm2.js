// packs/hbm2.js -- HBM2 content pack (JESD235D).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/hbm2); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'hbm2',
    name: 'HBM2',
    jedec: {
      doc: 'JESD235D',
      note: 'High Bandwidth Memory 2. Row timings are vendor-datasheet ' +
            'values; the standard defines symbol, unit and constraint. ' +
            'PC mode, BL4, separate row/column command buses.'
    },

    // Simplified drill topology: flat 8 banks, 8 rows, 8 cols, 2 Stack IDs.
    // Real parts: 8 channels/stack x 128 bit = 2 pseudo-channels of 64 bits;
    // 8/16/32/48 banks per pseudo-channel; stacks 4/8/12-high.
    topology: {
      hasBankGroups: false,
      groups: 1,
      banksPerGroup: 8,
      banks: 8,
      rows: 8,
      cols: 8,
      sids: 2
    },

    commands: ['ACT', 'PRE', 'RD', 'WR', 'RDA', 'WRA'],

    timingParams: [
      // --- chapter: core (row timings, per pseudo channel) -------------
      { symbol: 'tRCDRD', name: 'Row open to read legal',
        definition: 'ACT to RD/RDA, same bank. 14 nCK (14 ns) in the drill ' +
                    'model; vendor-datasheet value. The two-cycle ACT is ' +
                    'referenced at its second rising edge.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|RDA', scope: 'same_bank' }] },
      { symbol: 'tRCDWR', name: 'Row open to write legal',
        definition: 'ACT to WR/WRA, same bank. 14 nCK (14 ns) in the drill ' +
                    'model; vendor-datasheet value.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'WR|WRA', scope: 'same_bank' }] },
      { symbol: 'tRAS', name: 'Minimum row-open time',
        definition: 'ACT to PRE (or internal precharge of RDA/WRA), same ' +
                    'bank. 33 nCK (33 ns) in the drill model; max 9 x tREFI.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRP', name: 'Precharge to bank ready',
        definition: 'PRE to ACT (or REFSB), same bank. 14 nCK (14 ns) in the ' +
                    'drill model; vendor-datasheet value.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRC', name: 'Full activate cycle',
        definition: 'ACT to ACT, same bank. 47 nCK (47 ns) in the drill ' +
                    'model; equals tRAS + tRP by construction.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRRDL', name: 'Activate spacing, same bank group',
        definition: 'ACT to ACT (or REFSB) when both banks are in one ' +
                    'group. 6 nCK in the drill model; wider than tRRDS. ' +
                    'Never fires in the flat drill model, but encoded to match ' +
                    'the book tables.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_group' }] },
      { symbol: 'tRRDS', name: 'Activate spacing, different banks',
        definition: 'ACT to ACT (or REFSB) across different banks when bank ' +
                    'groups are disabled. 4 nCK in the drill model; this is ' +
                    'the flat-drill default.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_bank' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'No more than 4 ACT (or REFSB) commands in any ' +
                    'tFAW-wide rolling window. 40 nCK (40 ns) in the drill model.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRTPS', name: 'Read data to precharge, flat banks',
        definition: 'RD/RDA to PRE, same bank, with bank groups disabled. ' +
                    '4 nCK in the drill model. The book also defines tRTPL ' +
                    'for bank-group-enabled operation; the drill model uses ' +
                    'tRTPS.',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'Last write data to internal precharge legal. 18 nCK ' +
                    '(18 ns) in the drill model. The nCK twin WR is ' +
                    'programmed in MR1 OP[4:0]; feeds tDAL on WRA.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tDAL', name: 'Write auto-precharge total',
        definition: 'WRA to next ACT, same bank. 33 nCK in the drill model; ' +
                    'equals the programmed WR plus tRP in clocks and is also ' +
                    'bounded by tRC.',
        chapter: 'core',
        appliesTo: [{ from: 'WRA', to: 'ACT', scope: 'same_bank' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCDL', name: 'Column command spacing, same bank group',
        definition: 'RD->RD or WR->WR, both banks in one group. ' +
                    'MAX(4, 2.8 ns/tCK) nCK. Never fires in the flat drill, ' +
                    'but encoded to match the book tables.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'same_group' },
                    { from: 'WR|WRA', to: 'WR|WRA', scope: 'same_group' }] },
      { symbol: 'tCCDS', name: 'Column command spacing, different banks',
        definition: 'RD->RD or WR->WR across different banks when bank groups ' +
                    'are disabled. 2 nCK at BL4; 1 nCK at BL2. Direction ' +
                    'changes are governed by tRTW/tWTR.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'diff_bank' },
                    { from: 'WR|WRA', to: 'WR|WRA', scope: 'diff_bank' }] },
      { symbol: 'tCCDR', name: 'Read spacing across Stack IDs',
        definition: 'RD to RD crossing SIDs (8-high and taller). Replaces ' +
                    'tCCDS for seamless consecutive reads across SIDs; vendor ' +
                    'value in the 2-4 nCK range. Reads only - writes crossing ' +
                    'SIDs use tCCDS.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'diff_sid' }] },
      { symbol: 'tWTRL', name: 'Write to read, same bank group',
        definition: 'Internal write-to-read, banks in one group. Command-bus ' +
                    'form: WR -> RD = WL + BL/2 + tWTRL. Never fires in the ' +
                    'flat drill, but encoded to match the book tables.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'same_group' }] },
      { symbol: 'tWTRS', name: 'Write to read, different banks',
        definition: 'Internal write-to-read across different banks when bank ' +
                    'groups are disabled. Command-bus form: ' +
                    'WR -> RD = WL + BL/2 + tWTRS.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'diff_bank' }] },
      { symbol: 'tRTW', name: 'Read-to-write bus turnaround',
        definition: 'Not a DRAM array limit: the shared DQ/DBI/ECC pins ' +
                    'changing ownership. Controller-computed system bus-' +
                    'ownership rule: (RL + BL/2 - WL + tDQSS(min) + 0.5) x ' +
                    'tCK + tDQSCK(max) + tDQSQ(max), rounded up.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },

      // --- chapter: init (reference panel; MRS is not an engine cmd) ---
      { symbol: 'tMRD', name: 'Mode-register command spacing',
        definition: 'MRS to MRS. Minimum spacing between consecutive mode ' +
                    'register writes during init. Panel-only: the drill ' +
                    'engine does not emit MRS commands.',
        chapter: 'init',
        appliesTo: [{ from: 'MRS', to: 'MRS', scope: 'any' }] },
      { symbol: 'tMOD', name: 'Mode-register update delay',
        definition: 'MRS to any non-MRS command. Panel-only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRS', to: '*', scope: 'any' }] },

      // --- chapter: refresh (reference panel; engine never emits --------
      // --- REF/REFSB/SRX) ----------------------------------------------
      { symbol: 'tREFI', name: 'Average refresh interval',
        definition: 'REF to REF. 3.9 us max; 0.5x / 0.25x past vendor ' +
                    'temperature trip points. Up to 8 REF commands may be ' +
                    'postponed (9 x tREFI absolute bound). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFC', name: 'All-bank refresh cycle',
        definition: 'REF to next access. 110/160/260/350/450 ns for 1/2/4/8/' +
                    '16 Gb per channel. All banks precharged first. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'any' }] },
      { symbol: 'tRFCSB', name: 'Per-bank refresh cycle, same bank',
        definition: 'REFSB to next access of that bank. 160 ns for <=8 Gb/die, ' +
                    '200 ns for 12-16 Gb/die. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REFSB', to: '*', scope: 'same_bank' }] },
      { symbol: 'tRREFD', name: 'Per-bank refresh spacing, different banks',
        definition: 'REFSB to REFSB (or ACT) of a different bank. ' +
                    '8 ns. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REFSB', to: 'REFSB|ACT', scope: 'diff_bank' }] },
      { symbol: 'tREFISB', name: 'Average per-bank refresh interval',
        definition: 'Average REFSB rate: tREFI / N, where N is the number of ' +
                    'banks per pseudo-channel. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REFSB', to: 'REFSB', scope: 'any' }] },
      { symbol: 'tCKE', name: 'Minimum CKE pulse width',
        definition: 'Minimum CKE HIGH or LOW pulse width. MAX(7.5 ns, ' +
                    '5 x tCK). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] },
      { symbol: 'tXS', name: 'Self-refresh exit to non-DLL commands',
        definition: 'SRX to ACT, PRE, MRS or REF. MAX(5 x tCK, tRFC(min) + ' +
                    '10 ns). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: 'ACT|PRE|MRS|REF', scope: 'any' }] },
      { symbol: 'tXP', name: 'Power-down exit',
        definition: 'PDX to any valid command. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] }
    ],

    questionBank: [
      { q: 'In HBM2 pseudo-channel mode, which statement is true?',
        answers: [
          'BL4 is required, the two 64-bit PCs share CK/CKE/mode registers, and array timings are counted per PC',
          'BL2 is required and each PC has its own CK and CKE',
          'The two PCs are fully independent, including separate mode registers and command buses',
          'Pseudo-channel mode is only available on 4-die stacks'
        ],
        chapter: 'organization', hard: false,
        explanation: 'PC mode divides the 128-bit channel into two 64-bit pseudo-channels and requires BL4 (MR3 OP7 = 1). The PCs share CK, CKE, row/column command buses and mode registers, but each counts its own ACT-to-ACT and other array timings. BL2 is legacy mode, and PC mode is not tied to stack height.',
        source: 'JESD235D sec 3.1.2.2' },

      { q: 'Why can an HBM2 channel issue an ACT in the same cycle as a RD or WR?',
        answers: [
          'Row commands travel on the R bus while column commands travel on the separate C bus',
          'The ACT command is compressed into the read address bits',
          'PC0 handles row commands while PC1 handles column commands',
          'The base logic die serializes and re-issues both commands'
        ],
        chapter: 'organization', hard: false,
        explanation: 'Each channel has semi-independent row (R[6:0]) and column (C[8:0]) command buses. Because ACT/PRE/REF travel on R while RD/WR/MRS travel on C, a row command and a column command can be registered in the same cycle. The two PCs share both buses, and ACT is not compressed into column bits.',
        source: 'JESD235D sec 3.1.3' },

      { q: 'Which initialization step is characteristic of HBM2 compared with DDR3/DDR4?',
        answers: [
          'There is no DLL lock step and no ZQ calibration command; I/O impedance is calibrated during tINIT3',
          'The controller must issue a ZQCL command before the first MRS',
          'DLL reset is performed by MR0 A8 = 1 and then tDLLK is waited',
          'The IEEE 1500 port is mandatory and must finish before RESET_n is released'
        ],
        chapter: 'init', hard: false,
        explanation: 'HBM2 initialization has no DLL (therefore no DLL lock) and no ZQ calibration command; I/O calibration happens during tINIT3 while CKE is still LOW. The IEEE 1500 port is optional after tINIT3, not mandatory, and ZQCL/DLL reset do not exist in HBM2.',
        source: 'JESD235D sec 4.1' },

      { q: 'How are read latency and write latency programmed in HBM2?',
        answers: [
          'RL in MR2 OP[7:3], WL in MR2 OP[2:0], with ERL/EWL extensions in MR4 OP5/OP4',
          'Both RL and WL are programmed entirely in MR4',
          'RL is programmed by MR3 OP[5:0] and WL by MR1 OP[4:0]',
          'Latencies are fused at manufacturing and cannot be changed'
        ],
        chapter: 'init', hard: true,
        explanation: 'MR2 carries the base RL (OP[7:3]) and WL (OP[2:0]) fields. MR4 OP5 (ERL) and OP4 (EWL) extend the ranges to 34-48 nCK for RL and 9-16 nCK for WL. MR3 OP[5:0] is RAS, and MR1 OP[4:0] is write recovery WR.',
        source: 'JESD235D sec 5, Tables 11, 15' },

      { q: 'How is the auto-precharge variant of a read or write requested in HBM2?',
        answers: [
          'Set the C3 bit of the column command (RD becomes RDA, WR becomes WRA)',
          'Set the A10 bit, the same as DDR3/DDR4',
          'Use a separate WRA/RDA op-code on the row bus',
          'Auto-precharge is automatic for every BL4 access'
        ],
        chapter: 'commands', hard: false,
        explanation: 'HBM2 column commands use C3 as the auto-precharge flag. A10 is the DDR3/DDR4 convention and is not used on the HBM2 column bus; RDA/WRA are single column-bus op-codes selected by C3.',
        source: 'JESD235D sec 6.3.1, Tables 30-31' },

      { q: 'The activation timing for HBM2 is referenced at which point of the ACT command?',
        answers: [
          'The second rising edge of the two-cycle row-bus transfer',
          'The first rising edge of the two-cycle row-bus transfer',
          'The falling edge between the two ACT cycles',
          'The rising edge of the column command that follows'
        ],
        chapter: 'commands', hard: false,
        explanation: 'ACT is a two-cycle row-bus command; tRCD, tRAS and all other row timings reference the second rising CK edge of that transfer. The falling edge and the following column command are not the reference.',
        source: 'JESD235D sec 6.3.2.2' },

      { q: 'Two consecutive BL4 READs to different banks within the same Stack ID are spaced by...',
        answers: [
          'tCCDS = 2 nCK',
          'tCCDL = 4 nCK',
          'tCCDR',
          'tRTW'
        ],
        chapter: 'timing', hard: true,
        explanation: 'With bank groups disabled (the flat drill model), different-bank read-to-read spacing is tCCDS. At BL4 this is 2 nCK. tCCDL applies only when bank groups are enabled and both banks are in the same group, tCCDR applies only across different SIDs, and tRTW is read-to-write.',
        source: 'JESD235D Table 68, sec 6.3.3.2' },

      { q: 'A WRITE followed by a READ to different banks (bank groups disabled) must wait for...',
        answers: [
          'tWTRS = 4 nCK of internal write-to-read delay',
          'tWTRL = 6 nCK',
          'tCCDS = 2 nCK',
          'tRTW = 15 nCK'
        ],
        chapter: 'timing', hard: false,
        explanation: 'Different-bank write-to-read spacing with bank groups disabled is tWTRS. The command-bus form is WL + BL/2 + tWTRS. tWTRL is the same-group variant, tCCDS governs same-direction column commands, and tRTW is read-to-write.',
        source: 'JESD235D Table 68, sec 6.3.3.3' },

      { q: 'The minimum ACT-to-ACT time on the same bank is governed by which relation?',
        answers: [
          'tRC = tRAS + tRP',
          'tRC = tRCDRD + tRTPS',
          'tRC = 4 x tRRDS',
          'tRC is an independent vendor value unrelated to tRAS and tRP'
        ],
        chapter: 'timing', hard: false,
        explanation: 'tRC bounds ACT-to-ACT on one bank and must cover tRAS (earliest legal PRE) plus tRP (precharge to ready). The canonical cycle is ACT -> (tRAS) -> PRE -> (tRP) -> ACT. tRRDS is for different banks, and tRCDRD/tRTPS are column/precharge paths.',
        source: 'JESD235D Table 68, sec 6.3.2.2' },

      { q: 'tRTW on HBM2 is best described as...',
        answers: [
          'A controller-computed system bus-ownership rule, not a DRAM array limit',
          'A fixed 2 nCK bus turnaround like tCCDS',
          'A DRAM array limit between read data and the next write command',
          'The read postamble length of RDQS'
        ],
        chapter: 'timing', hard: true,
        explanation: 'tRTW is NOT a DRAM array limit; it is the time the shared bidirectional DQ/DBI/ECC pins need to change ownership. The minimum is computed from RL, WL, BL and strobe timings and rounded up. Because it depends on system latencies, two controllers with different MR programming may need different tRTW.',
        source: 'JESD235D Table 68 NOTE 23' },

      { q: 'Which data-integrity statement is correct for HBM2?',
        answers: [
          'Link ECC is optional (one bit per byte), generated by the host; there is no on-die ECC',
          'On-die ECC is mandatory and corrects single-bit errors inside the array',
          'DBIac is mandatory on every transfer',
          'CRC covers both read and write data by default'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'HBM2 offers optional link ECC (one ECC pin per 8 DQ) that the host must generate and check; the DRAM array has no on-die ECC. DBIac is mode-register selectable, not mandatory. CRC is not a default HBM2 feature.',
        source: 'JESD235D sec 6.2.2, 6.2.4' },

      { q: 'How are the HBM2 data, command and clock interfaces terminated?',
        answers: [
          'They are unterminated; there is no ODT pin or on-die termination',
          'A dynamic ODT value is selected in MR1 for writes',
          'Rtt_NOM and Rtt_WR are programmed through MR1 and MR2',
          'Termination is controlled by an ODT pin sampled during ACT commands'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'HBM2 uses unterminated data, command, address and clock interfaces. There is no ODT pin and no on-die termination; signal integrity is handled by driver strength (MR1) and system-level design. Rtt_NOM/Rtt_WR and ODT pins belong to DDR3/DDR4.',
        source: 'JESD235D sec 2, 6.4' },

      { q: 'What is the difference between REF and REFSB in HBM2?',
        answers: [
          'REF refreshes all banks and needs tRFC; REFSB refreshes one bank while the others remain available',
          'REF is per-bank and REFSB is all-bank',
          'Both commands refresh the same bank count but use different internal counters',
          'REFSB is not allowed in pseudo-channel mode'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'REF is an all-bank refresh: every bank must be precharged and the device is busy for tRFC. REFSB (single-bank refresh) targets one bank; other banks can still be accessed, gated by tRFCSB for that bank and tRREFD to a different bank. REFSB is fully supported in PC mode.',
        source: 'JESD235D sec 6.3.2.5, 6.3.2.6' },

      { q: 'What is the maximum average interval between HBM2 REFRESH commands, and what happens if the controller falls behind?',
        answers: [
          'tREFI = 3.9 us; up to 8 REF commands may be postponed, so the worst gap is 9 x tREFI',
          'tREFI = 7.8 us; only 1 REF may be postponed',
          'tREFI = 3.9 us and no postponement is allowed',
          'The controller may skip refreshes entirely below 45 C'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'The average refresh interval is 3.9 us. To allow burst/pause patterns, up to 8 REF commands can be postponed, giving a 9 x tREFI absolute maximum between REF commands. The interval shortens to 0.5x/0.25x at vendor temperature trip points.',
        source: 'JESD235D Table 68 NOTE 28' },

      { q: 'HBM2 does not define a Refresh Management (RFM) command. What does it use for row-disturb mitigation instead?',
        answers: [
          'Target Row Refresh (TRR) mode, with vendor-defined tMAW/MAC limits',
          'On-die ECC scrubbing',
          'A periodic REF rate doubling',
          'Bank grouping, which naturally spreads activate current'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'HBM2 has no RFM command. Row-disturb mitigation is handled by TRR mode (MR5 selects the target bank), governed by vendor-defined Maximum Activate Window (tMAW) and Maximum Activate Count (MAC) values. On-die ECC does not exist in HBM2, and bank grouping is unrelated to refresh management.',
        source: 'JESD235D sec 6.6' }
    ],

    commandDocs: [
      { cmd: 'ACT', name: 'Activate',
        description: 'Opens row R in bank B (SID acts as extra bank address ' +
                     'on high stacks). Travels on the R bus over two cycles - ' +
                     'all row timings reference the second rising edge. ' +
                     'Spacing: tRCDRD/tRCDWR to the first column command, ' +
                     'tRRDS/tRRDL to the next ACT, tFAW across any four, tRC ' +
                     'same bank.' },
      { cmd: 'RD', name: 'Read (BL4 fixed)',
        description: 'Bursts 4 words from the open row on the C bus; C3 = 0. ' +
                     'Data begins RL cycles after the command. Same-direction ' +
                     'spacing tCCDS/tCCDL (tCCDR across SIDs), tRTW to a ' +
                     'write, tWTRS/tWTRL from a write.' },
      { cmd: 'RDA', name: 'Read with Auto-Precharge',
        description: 'RD with C3 = 1: the bank precharges itself at tRTPS ' +
                     '(tRTPL with bank groups enabled) after the burst, once ' +
                     'tRAS is met. Re-activation waits tRP and tRC.' },
      { cmd: 'WR', name: 'Write (BL4 fixed)',
        description: 'Bursts 4 words into the open row; first data is ' +
                     'captured WL cycles after the command, C3 = 0. ' +
                     'Write-to-write spacing is tCCDS/tCCDL.' },
      { cmd: 'WRA', name: 'Write with Auto-Precharge',
        description: 'WR with C3 = 1: the bank precharges itself after ' +
                     'WL + BL/2 + WR clocks, once tRAS is met. Next ACT ' +
                     'waits tRP and tRC.' },
      { cmd: 'PRE', name: 'Precharge Per-Bank / All-Bank',
        description: 'PREpb closes the open row of one bank; PREab closes ' +
                     'every bank of the pseudo-channel. One cycle on the R ' +
                     'bus. Bank ready again after tRP.' },
      { cmd: 'REF/REFAB', name: 'All-Bank Refresh',
        description: 'One all-bank refresh step; every bank precharged first, ' +
                     'die busy tRFC. Average rate tREFI (3.9 us max, shortened ' +
                     'past temperature trip points); up to 8 may be postponed.' },
      { cmd: 'REFSB', name: 'Single-Bank Refresh',
        description: 'Refreshes one bank for tRFCSB while the others stay ' +
                     'schedulable. Counts against tFAW like an ACT; tRREFD ' +
                     'spaces REFSB to a different bank. The per-bank counter ' +
                     'resets after a full set of REFSBs, a REF, or SRE.' },
      { cmd: 'MRS', name: 'Mode Register Set',
        description: 'Column-bus command writing one of the mode registers. ' +
                     'All banks idle; spacing tMRD/tMOD around it. Carries RL, ' +
                     'WL, ERL/EWL, BL, bank-group enable, DBI/ECC/DM, parity, ' +
                     'and TRR options.' },
      { cmd: 'SRE/SRX', name: 'Self-Refresh Entry / Exit',
        description: 'Row-bus commands: SRE enters self-refresh (all banks ' +
                     'idle, bursts drained, tMOD met) with the internal clock ' +
                     'stopped. SRX exits; commands are legal after tXS, MRS ' +
                     'after tXSMRS.' },
      { cmd: 'PDE/PDX', name: 'Power-Down Entry / Exit',
        description: 'Row-bus commands: PDE parks the channel in precharge or ' +
                     'active power-down. Not legal during a burst. PDX exits; ' +
                     'commands are legal tXP later. CK may stop after tCPDED ' +
                     'and must be stable tCKSRX before exit.' },
      { cmd: 'NOP/DES', name: 'Row/Column No-Operation',
        description: 'RNOP parks the row bus and CNOP parks the column bus, ' +
                     'so one bus can idle while the other works (for example, ' +
                     'an ACT on R with a CNOP on C in the same cycle).' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: ['sid'],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
