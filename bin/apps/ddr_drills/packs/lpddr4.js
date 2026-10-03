// packs/lpddr4.js -- LPDDR4 content pack (JESD209-4E).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/lpddr4); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
//
// LPDDR4 is a FLAT topology in the drill model: no bank groups, no Stack IDs.
// Scopes used: same_bank / diff_bank / any. The real die contains two
// independent channels; this pack models one channel.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'lpddr4',
    name: 'LPDDR4',
    jedec: {
      doc: 'JESD209-4E',
      note: 'Low Power DDR4. Dual-channel die, 16n prefetch, BL16 primary, ' +
            'no DLL with programmed RL/WL, masked write + DBI, Refresh ' +
            'Management (RFM), Frequency Set Points (FSP).'
    },

    // Simplified drill topology: 8 flat banks, 8 rows, 8 cols. Real parts
    // are dual-channel dies; the two channels share only package pins such
    // as RESET_n and ZQ and schedule independently.
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
                    'column command. max(18 ns, 4 nCK) in x16 mode.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tRPpb', name: 'Precharge time, one bank',
        definition: 'PRE (single bank) to ACT of that bank. max(18 ns, 4 nCK) ' +
                    'in x16 mode.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRPab', name: 'Precharge time, all banks',
        definition: 'PRE-all to ACT of any bank. max(21 ns, 4 nCK) in x16 ' +
                    'mode; longer than tRPpb on 8-bank devices. Panel only - ' +
                    'the drill model\'s PRE is per-bank.',
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
        definition: 'ACT to ACT, different banks. max(10 ns, 4 nCK), relaxed ' +
                    'to max(7.5 ns, 4 nCK) at 4267 Mb/s; a REFpb counts as ' +
                    'an activation for tFAW.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_bank' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'At most 4 ACTs (or REFpb operations) in any rolling ' +
                    'window. 40 ns at most speeds, 30 ns at 4267 Mb/s.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRTP', name: 'Read to precharge',
        definition: 'RD/RDA to PRE, same bank: last-prefetch analog delay. ' +
                    'max(7.5 ns, 8 nCK); command form BL/2 + max(8, ' +
                    'RU(tRTP/tCK)) - 8.',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'WR/WRA to PRE, same bank. max(18 ns, 6 nCK) for x16; ' +
                    'max(20 ns, 6 nCK) for x8. The nWR field carries the ' +
                    'programmed clocks for auto-precharge.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tPPD', name: 'Precharge-to-precharge spacing',
        definition: 'PRE to PRE, same channel. 4 nCK minimum between ' +
                    'back-to-back PRE commands; does not apply to ' +
                    'auto-precharges.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'PRE', scope: 'any' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCD', name: 'Column-to-column spacing',
        definition: 'Same-direction column commands, any banks: 8 tCK for ' +
                    'BL16, 16 tCK for BL32. BL16 occupies 8 clocks of DQ, so ' +
                    'back-to-back BL16 bursts saturate the bus.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'any' },
                    { from: 'WR|WRA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tWTR', name: 'Write-to-read delay',
        definition: 'End of write burst data to RD. max(10 ns, 8 nCK) for ' +
                    'x16; max(12 ns, 8 nCK) for x8; command form WL + 1 + ' +
                    'BL/2 + RU(tWTR/tCK).',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'any' }] },
      { symbol: 'tRTW', name: 'Read-to-write turnaround',
        definition: 'Named in JESD209-4E. The loose read strobe (no DLL) plus ' +
                    'the burst must clear before the write preamble. Command ' +
                    'gap = RL + RU(tDQSCK(MAX)/tCK) + BL/2 - WL + tWPRE + ' +
                    'RU(tRPST).',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },

      // --- chapter: init (reference panel; MRW/MRR are not engine cmds) -
      { symbol: 'tMRW', name: 'Mode-register write command period',
        definition: 'MRW to MRW. max(10 ns, 10 tCK); only DES is allowed ' +
                    'during tMRW. Panel only - the drill engine does not emit ' +
                    'MRW.',
        chapter: 'init',
        appliesTo: [{ from: 'MRW', to: 'MRW', scope: 'any' }] },
      { symbol: 'tMRR', name: 'Mode-register read command period',
        definition: 'MRR to MRR. 8 tCK; only DES is allowed during tMRR. ' +
                    'Panel only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRR', to: 'MRR', scope: 'any' }] },
      { symbol: 'tMRD', name: 'Mode-register command spacing',
        definition: 'MRW to the next valid non-MRW command. max(14 ns, 10 ' +
                    'nCK). Panel only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRW', to: '*', scope: 'any' }] },

      // --- chapter: refresh (reference panel; REF/SRX are engine-only) -
      { symbol: 'tREFI', name: 'Average refresh interval',
        definition: 'Average REFab interval: 3.904 us at 1x rate (8192 ' +
                    'REFab per 32 ms tREFW), halved above 85 C. Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tREFW', name: 'Refresh window',
        definition: 'Rolling window in which 8192 REFab commands must be ' +
                    'distributed: 32 ms at 1x rate. Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFCab', name: 'All-bank refresh cycle',
        definition: 'REFab to next command, device busy. 130 ns (1-2 Gb/ch), ' +
                    '180 ns (3-4), 280 ns (6-8), 380 ns (12-16). Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'any' }] },
      { symbol: 'tRFCpb', name: 'Per-bank refresh cycle',
        definition: 'REFpb to ACT of the same bank or the next REFpb. 60 ns ' +
                    '(1-2 Gb/ch), 90 ns (3-4), 140 ns (6-8), 190 ns (12-16). ' +
                    'Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REFpb', to: 'ACT|REFpb', scope: 'same_bank' }] },
      { symbol: 'tXSR', name: 'Self-refresh exit to command',
        definition: 'SRX to any valid command. max(tRFCab + 7.5 ns, 2 nCK). ' +
                    'No DLL re-lock wait is needed (LPDDR4 has no DLL). ' +
                    'Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] },
      { symbol: 'tXP', name: 'Power-down exit',
        definition: 'PDX to any valid command. max(7.5 ns, 5 nCK). Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] }
    ],

    questionBank: [
      { q: 'What is the LPDDR4 prefetch width, and what is the primary burst length?',
        answers: [
          '16n prefetch with BL16 as the primary burst',
          '8n prefetch with BL8 as the primary burst',
          '16n prefetch with BL8 as the primary burst',
          '8n prefetch with BL16 as the primary burst'
        ],
        chapter: 'organization', hard: false,
        explanation: 'LPDDR4 uses a 16n prefetch and BL16 as the baseline. BL32 and on-the-fly BL16/BL32 are also programmable, but there is no burst chop and no interleaved burst type.',
        source: 'JESD209-4E sec 2.1' },

      { q: 'How many banks does an LPDDR4 channel contain, and are they arranged in bank groups?',
        answers: [
          'Eight independent banks with no bank groups',
          'Eight banks arranged in two bank groups of four',
          'Sixteen banks in four bank groups',
          'Four banks with no groups'
        ],
        chapter: 'organization', hard: false,
        explanation: 'Every LPDDR4 channel has eight flat banks (BA0-BA2). The spec does not define 4-bank or bank-group LPDDR4 devices.',
        source: 'JESD209-4E sec 2.1' },

      { q: 'How is a full device reset performed in LPDDR4?',
        answers: [
          'By driving the dedicated RESET_n pin low for at least 200 us after supplies are stable',
          'By an MRW to a reset register, as in LPDDR3',
          'By holding CKE low for 2 ms with no clock',
          'By issuing PREA followed by REFab'
        ],
        chapter: 'init', hard: false,
        explanation: 'LPDDR4 adds a dedicated RESET_n pin. The reset-while-power-stable sequence uses RESET_n low for at least 100 ns, then repeats the normal init steps. LPDDR3 used an MRW to MR63 because it lacked a reset pin.',
        source: 'JESD209-4E sec 3.3.1' },

      { q: 'After RESET_n rises in a cold LPDDR4 start, what is the first required step before configuration MRWs?',
        answers: [
          'Wait at least 2 ms, then raise CKE with a stable clock for at least 5 tCK, then issue DES for 2 us',
          'Issue MRW commands immediately',
          'Begin ZQ calibration before CKE rises',
          'Start command-bus training before the clock is stable'
        ],
        chapter: 'init', hard: false,
        explanation: 'The fixed sequence after RESET_n rises is: wait tINIT3 = 2 ms, raise CKE only after the clock has been stable for tINIT4 = 5 tCK, then issue DES for tINIT5 = 2 us before the first configuration MRW.',
        source: 'JESD209-4E sec 3.3.1' },

      { q: 'Where are LPDDR4 read latency (RL) and write latency (WL) programmed?',
        answers: [
          'MR2: RL in OP[2:0] and WL in the same field, with WL Set A/B selected by OP[6]',
          'MR1, next to the burst-length and nWR fields',
          'They are fixed by the speed grade and cannot be changed',
          'MR0, which is read-only device information'
        ],
        chapter: 'init', hard: false,
        explanation: 'MR2 carries the RL/WL pairs. MR1 carries BL, nWR, and preamble/post-amble settings. MR0 is read-only device information. The controller chooses the RL/WL pair to match the clock rate.',
        source: 'JESD209-4E sec 3.4.1 (MR2)' },

      { q: 'Why does LPDDR4 name the read-to-write parameter tRTW while earlier low-power generations did not?',
        answers: [
          'Because there is no DLL, the read strobe has a wide tDQSCK window that must be absorbed before write data may drive',
          'Because the burst length doubled to BL16',
          'Because write DBI changes the write preamble',
          'Because the CA bus shrank to 6 bits'
        ],
        chapter: 'timing', hard: true,
        explanation: 'Without a DLL the read strobe arrival is an analog window relative to CK, and the controller must budget the worst case. That wander term appears explicitly in the tRTW formula. BL16, DBI, and the 6-bit CA bus are unrelated to why the symbol is named.',
        source: 'JESD209-4E sec 4.35' },

      { q: 'What is the LPDDR4 tRTW formula (DQ ODT disabled)?',
        answers: [
          'RL + RU(tDQSCK(MAX)/tCK) + BL/2 - WL + tWPRE + RU(tRPST)',
          'WL + 1 + BL/2 + RU(tWTR/tCK)',
          'BL/2 + 2 clocks',
          'tCCD + tWTR'
        ],
        chapter: 'timing', hard: true,
        explanation: 'JESD209-4E names tRTW and gives RL + RU(tDQSCK(MAX)/tCK) + BL/2 - WL + tWPRE + RU(tRPST). WL + 1 + BL/2 + RU(tWTR/tCK) is the write-to-read direction, and tCCD is same-direction column spacing.',
        source: 'JESD209-4E sec 4.35' },

      { q: 'What is the LPDDR4 column-to-column spacing tCCD for a BL16 burst?',
        answers: [
          '8 tCK',
          '4 tCK',
          '16 tCK',
          '2 tCK'
        ],
        chapter: 'timing', hard: false,
        explanation: 'BL16 occupies 8 clocks of DQ, so tCCD = 8 tCK for same-direction column commands. BL32 uses 16 tCK. There is no burst chop.',
        source: 'JESD209-4E sec 4.10' },

      { q: 'Which command must be used when a write masks at least one beat in LPDDR4?',
        answers: [
          'Masked Write (MWR-1 + CAS-2), because LPDDR4 has no dedicated DM pin',
          'A normal Write with the DM pin held high',
          'MPC Write FIFO',
          'MRW to the data-mask register'
        ],
        chapter: 'commands', hard: false,
        explanation: 'LPDDR4 has no dedicated DM pin. Masking is performed with the Masked Write command and the DMI pin per byte lane. Plain writes must drive DMI low when masking is disabled.',
        source: 'JESD209-4E sec 4.13' },

      { q: 'What does the LPDDR4 DMI pin carry?',
        answers: [
          'Data-mask information for masked writes and DBI status for reads and writes, depending on mode-register settings',
          'The chip-select signal',
          'The CA parity bit',
          'The write-CRC checksum'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'DMI is bidirectional per byte lane. With masked writes it carries mask; with write DBI it tells the DRAM whether to invert; with read DBI it tells the controller whether the byte was inverted. LPDDR4 has no CA parity and no write CRC.',
        source: 'JESD209-4E sec 4.15' },

      { q: 'Which statement about LPDDR4 data integrity is correct?',
        answers: [
          'LPDDR4 has no write CRC and no CA parity; DBI limits ones on the bus for power and DC balance',
          'Write CRC is mandatory and reported on ALERT_n',
          'CA parity is optional and logged in MPR page 1',
          'On-die ECC is required for all densities'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'LPDDR4 relies on DBI plus system-level schemes. It has no write CRC, no CA parity, and no on-die ECC. Those features belong to DDR4 or HBM.',
        source: 'JESD209-4E sec 4.15' },

      { q: 'What is the LPDDR4 1x-mode average refresh interval, and how does it compare to LPDDR3?',
        answers: [
          '3.904 us, half of LPDDR3\'s 7.8 us, because LPDDR4 requires 8192 REFab per 32 ms',
          '7.8 us, the same as LPDDR3',
          '1.95 us, one quarter of LPDDR3',
          '15.6 us, twice LPDDR3'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'LPDDR4 doubles the refresh command count to 8192 per 32 ms window versus LPDDR3\'s 4096, so the average interval is 3.904 us. Above 85 C the rate doubles again.',
        source: 'JESD209-4E sec 4.19' },

      { q: 'What triggers the need for an LPDDR4 Refresh Management (RFM) command?',
        answers: [
          'A per-bank rolling accumulated ACT (RAA) counter reaching the RAAIMT threshold',
          'tREFI expiring',
          'A temperature-compensated refresh multiplier change',
          'A write CRC error'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'RFM is driven by the RAA counter, which increments per ACT per bank. When RAA reaches RAAIMT (reported in MR24) the controller must issue RFMab or RFMpb before RAAMMT is reached. It is independent of tREFI and refresh multipliers.',
        source: 'JESD209-4E sec 4.47' },

      { q: 'How do the two channels of a dual-channel LPDDR4 die share refresh?',
        answers: [
          'They do not share refresh; each channel has an independent refresh schedule',
          'They share a single refresh counter and tRFC window',
          'Channel A refreshes the lower four banks and channel B the upper four',
          'Both channels must issue REFab in the same clock cycle'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'Each channel of a dual-channel die has its own CA bus, clock, CKE, CS, and DQ, and schedules its own refresh independently. The only shared package pins are RESET_n and ZQ.',
        source: 'JESD209-4E sec 2.1' },

      { q: 'Which power state was removed from the user-visible command set in LPDDR4 compared with LPDDR3?',
        answers: [
          'Deep power-down (DPD); LPDDR4 relies on FSP and power-down instead',
          'Self-refresh',
          'Active power-down',
          'Precharge power-down'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'LPDDR4 drops the data-losing deep power-down state that LPDDR3 had. The mobile power story is now Frequency Set Points for fast DVFS plus active/precharge power-down.',
        source: 'JESD209-4E sec 4.21' }
    ],

    commandDocs: [
      { cmd: 'ACT', name: 'Activate',
        description: 'Opens row R in bank B. The command is issued as ACT-1 ' +
                     'followed immediately by ACT-2 on the 6-bit CA bus; the ' +
                     'row address is split across both cycles and the bank ' +
                     'address is carried in ACT-1. Spacing: tRCD to the first ' +
                     'RD/WR, tRRD to the next ACT, tFAW across any four, tRC ' +
                     'same bank.' },
      { cmd: 'RD', name: 'Read',
        description: 'Starts a BL16 or BL32 read burst from the open row. ' +
                     'RD-1 is immediately followed by CAS-2. Data returns RL ' +
                     'clocks later plus the wide tDQSCK window. Same-direction ' +
                     'spacing tCCD = 8 clocks (BL16); tRTW to a write.' },
      { cmd: 'WR', name: 'Write',
        description: 'Starts a BL16 or BL32 write burst. WR-1 is immediately ' +
                     'followed by CAS-2. First data is captured WL clocks ' +
                     'after the command. Use Masked Write when any beat must ' +
                     'be masked. Same-direction spacing tCCD; tWTR to a read.' },
      { cmd: 'RDA', name: 'Read with Auto-Precharge',
        description: 'RD with AP = 1: the bank precharges itself once tRAS ' +
                     'and tRTP are met. Re-activation waits tRPpb and tRC ' +
                     'from the old ACT.' },
      { cmd: 'WRA', name: 'Write with Auto-Precharge',
        description: 'WR with AP = 1: the bank precharges itself after write ' +
                     'recovery (WL + 1 + BL/2 + nWR past the command). ' +
                     'Re-activation waits tRPpb and tRC.' },
      { cmd: 'PRE', name: 'Precharge',
        description: 'Closes the open row of one bank or all banks. AB = 1 ' +
                     'precharges all banks (tRPab); AB = 0 precharges the bank ' +
                     'selected by BA[2:0] (tRPpb). Must not violate tRAS, ' +
                     'tRTP, or tWR.' },
      { cmd: 'MRR', name: 'Mode Register Read',
        description: 'Reads one of 64 mode registers back onto DQ[7:0] ' +
                     'during the first 4 UI of a BL16 burst. MRR-1 is ' +
                     'followed by CAS-2. Only DES is allowed during the tMRR ' +
                     'window.' },
      { cmd: 'MRW', name: 'Mode Register Write',
        description: 'Two-cycle command (MRW-1 + MRW-2) carrying 8-bit ' +
                     'register address and 8-bit operand. All banks must be ' +
                     'idle; tMRW between MRWs, tMRD to the next non-MRW ' +
                     'command. Carries BL, RL/WL, nWR, DBI, ODT, FSP, and ' +
                     'training controls.' },
      { cmd: 'MPC', name: 'Multi-Purpose Command',
        description: 'Provides NOP (OP6 = 0) and training/calibration ' +
                     'operations. Write FIFO, Read FIFO, and Read DQ ' +
                     'Calibration require CAS-2 immediately after MPC. ZQCal ' +
                     'Start/Latch and DQS oscillator start/stop need two ' +
                     'additional DES/NOP cycles. RFM is also issued through ' +
                     'the REF encoding when RFM is required.' },
      { cmd: 'REFab/REFpb', name: 'Refresh All Banks / Per Bank',
        description: 'REFab refreshes every bank and needs all banks idle; ' +
                     'wait tRFCab. REFpb refreshes the addressed bank; wait ' +
                     'tRFCpb for that bank or tRRD for a different bank. ' +
                     'Eight REFpb operations replace one REFab of refresh ' +
                     'coverage. Up to 8 REFab may be postponed or pulled in.' },
      { cmd: 'RFM', name: 'Refresh Management',
        description: 'Extra refresh-like command required when a per-bank ' +
                     'rolling accumulated ACT count (RAA) reaches the RAAIMT ' +
                     'threshold reported in MR24. RFMab decrements all banks; ' +
                     'RFMpb decrements one bank. Obey the same minimum ' +
                     'separations as REF.' },
      { cmd: 'SRE/SRX', name: 'Self-Refresh Entry / Exit',
        description: 'Entry: SRE encoding with all banks idle and CKE ' +
                     'falling. Exit: CKE rises with stable clock; wait tXSR ' +
                     'to any valid command. At least one extra refresh (one ' +
                     'REFab or eight REFpb) must be issued before re-entering.' },
      { cmd: 'PDE/PDX', name: 'Power-Down Entry / Exit',
        description: 'CKE low parks the channel in active or idle power-down. ' +
                     'No refresh occurs, so dwell time is bounded by the ' +
                     'refresh schedule. Exit: CKE rises; first valid command ' +
                     'after tXP.' },
      { cmd: 'NOP', name: 'No Operation / Deselect',
        description: 'DES (CS low for one cycle) holds the bus idle and ' +
                     'never aborts an in-flight operation. MPC with OP6 = 0 ' +
                     'acts as a two-cycle NOP. Used to fill forced gaps such ' +
                     'as tRRD, tCCD, tMRW, and turnaround bubbles.' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: [],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
