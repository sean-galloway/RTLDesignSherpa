// packs/lpddr3.js -- LPDDR3 content pack (JESD209-3C).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/lpddr3); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
//
// LPDDR3 is a FLAT topology: no bank groups, no Stack IDs. Scopes used
// in appliesTo are therefore same_bank / diff_bank / any only.
// tCCD is modeled same-direction only, matching the book's gap sheet -
// direction changes use the formula-based turnaround rules, which always
// dominate tCCD there. tRPpab (all-bank precharge) is reference-panel
// only: the drill model's PRE is per-bank, so it uses tRPpb.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'lpddr3',
    name: 'LPDDR3',
    jedec: {
      doc: 'JESD209-3C',
      note: 'Low Power DDR3. 8n prefetch, fixed BL8, no DLL with programmed ' +
            'RL/WL, HSUL_12 unterminated interface, per-bank refresh and ' +
            'precharge, MRR/MRW mode-register access, CA training, deep ' +
            'power-down.'
    },

    // Simplified drill topology: 8 banks, 8 rows, 8 cols, flat. Real
    // parts: x16 and x32 organizations, densities from 1 Gb to 32 Gb,
    // all with 8 banks and no bank groups.
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
        definition: 'ACT to RD/WR, same bank: row open to first column ' +
                    'command. 15/18/24 ns by bin, min 3 tCK.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tRAS', name: 'Minimum row-active time',
        definition: 'ACT to PRE, same bank. Min max(42 ns, 3 tCK); max ' +
                    'min(70.2 us, 9 x RM x tREFI).',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRPpb', name: 'Precharge time, one bank',
        definition: 'PRE (single bank) to ACT of that bank. 15/18/24 ns, ' +
                    'min 3 tCK.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRPpab', name: 'Precharge time, all banks',
        definition: 'PRE-all to ACT of any bank. 18/21/27 ns, min 3 tCK; ' +
                    'longer than tRPpb on 8-bank devices. Panel only - the ' +
                    'drill model\'s PRE is per-bank.',
        chapter: 'core',
        appliesTo: [{ from: 'PREA', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRC', name: 'Row cycle',
        definition: 'ACT to ACT, same bank: tRAS + tRPpb (or tRAS + tRPpab ' +
                    'after a PRE-all).',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRRD', name: 'Activate spacing, different banks',
        definition: 'ACT to ACT, different banks. 10 ns, min 2 tCK. A ' +
                    'REFpb counts as an activation for tFAW.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_bank' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'At most 4 ACTs (or REFpb operations) in any rolling ' +
                    'window. 50 ns, min 8 tCK.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRTP', name: 'Read to precharge',
        definition: 'RD to PRE, same bank: last-prefetch analog delay. ' +
                    '7.5 ns, min 4 tCK; command form BL/2 + max(4, ' +
                    'RU(tRTP/tCK)) - 4.',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'Last write data to PRE, same bank. 15 ns, min 4 tCK; ' +
                    'the MR1 nWR field carries RU(tWR/tCK) for auto-precharge.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCD', name: 'Column-to-column spacing',
        definition: 'Same-direction column commands, any banks: 4 tCK = BL/2. ' +
                    'Direction changes use the turnaround formulas instead.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'any' },
                    { from: 'WR|WRA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tWTR', name: 'Write-to-read delay',
        definition: 'End of write burst data to RD. 7.5 ns, min 4 tCK; ' +
                    'command form WL + 1 + BL/2 + RU(tWTR/tCK).',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'any' }] },
      { symbol: 'tRTW', name: 'Read-to-write turnaround',
        definition: 'Book symbol - JESD209-3C gives the rule unnamed, as a ' +
                    'formula: RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL clocks. ' +
                    'The tDQSCK dependence is the LPDDR3 signature: no DLL, ' +
                    'so the multi-clock read-strobe wander must be absorbed ' +
                    'before write data may drive.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },

      // --- chapter: init (reference panel; MRW/MRR are not engine cmds) -
      { symbol: 'tMRW', name: 'Mode-register write command period',
        definition: 'MRW to MRW. 10 tCK; only NOP is allowed during tMRW. ' +
                    'Panel only - the drill engine does not emit MRW.',
        chapter: 'init',
        appliesTo: [{ from: 'MRW', to: 'MRW', scope: 'any' }] },
      { symbol: 'tMRR', name: 'Mode-register read command period',
        definition: 'MRR to MRR. 4 tCK; only NOP is allowed during tMRR. ' +
                    'Panel only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRR', to: 'MRR', scope: 'any' }] },
      { symbol: 'tMRD', name: 'Mode-register command spacing',
        definition: 'MRW to the next valid non-MRW command. max(14 ns, 10 ' +
                    'nCK). Panel only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRW', to: '*', scope: 'any' }] },

      // --- chapter: refresh (reference panel; REF/SRX are engine-only) -
      { symbol: 'tREFI', name: 'Average refresh interval (reference)',
        definition: 'Average REFab interval: 7.8 us at <=85 C. The real ' +
                    'contract is R refreshes in every rolling tREFW (32 ms). ' +
                    'Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFCab', name: 'All-bank refresh cycle',
        definition: 'REFab to next command, device busy. 130 ns (1-4 Gb), ' +
                    '210 ns (6-8 Gb). Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF|ACT', scope: 'any' }] },
      { symbol: 'tRFCpb', name: 'Per-bank refresh cycle',
        definition: 'REFpb to ACT of the same bank or the next REFpb. 60 ns ' +
                    '(1-4 Gb), 90 ns (6-8 Gb). Only the target bank is busy; ' +
                    'a different bank needs just tRRD. 8 REFpb replace one ' +
                    'REFab. Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REFpb', to: 'ACT|REFpb', scope: 'same_bank' }] },
      { symbol: 'tXSR', name: 'Self-refresh exit to command',
        definition: 'SRX to any valid command. max(tRFCab + 10 ns, 2 nCK). ' +
                    'No DLL re-lock wait is needed (LPDDR3 has no DLL). ' +
                    'Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] },
      { symbol: 'tXP', name: 'Power-down exit',
        definition: 'PDX to any valid command. max(7.5 ns, 3 nCK). Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] },
      { symbol: 'tCKE', name: 'Minimum CKE pulse width',
        definition: 'Minimum high or low pulse width on CKE. max(7.5 ns, ' +
                    '3 nCK). Panel only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] }
    ],

    questionBank: [
      { q: 'What is the prefetch width of LPDDR3, and what does it imply for the minimum burst?',
        answers: [
          '8n prefetch: each column access moves 8 words per DQ, so a BL8 burst occupies 4 clocks on the DDR bus',
          '4n prefetch: a BL8 burst occupies 2 clocks',
          '2n prefetch: a BL8 burst occupies 1 clock',
          'The prefetch is programmable between 2n and 8n'
        ],
        chapter: 'organization', hard: false,
        explanation: 'LPDDR3 uses a fixed 8n prefetch. The DDR interface delivers 2 words per DQ per clock, so BL8 = 8 words / 2 words per clock = 4 clocks. LPDDR2-S4 was 4n (2 clocks); LPDDR2-S2 was 2n (1 clock).',
        source: 'JESD209-3C sec 2.4, Table 64' },

      { q: 'How many valid burst lengths does LPDDR3 support?',
        answers: [
          'One: BL8 is fixed; all other MR1 burst-length encodings are reserved',
          'Two: BL8 and BC4 burst chop',
          'Four: BL4, BL8, BL16 and on-the-fly',
          'Eight: any power-of-two length from BL2 to BL16'
        ],
        chapter: 'organization', hard: false,
        explanation: 'BL8 is the only supported burst length in LPDDR3. There is no burst chop, no burst terminate, and no interleaved burst type. MR1 OP2:0 = 011B selects BL8; other codes are reserved.',
        source: 'JESD209-3C sec 3.4.1 (MR1)' },

      { q: 'LPDDR3 has no dedicated SDRAM RESET# pin. How is a reset performed?',
        answers: [
          'By an MRW to the reset register (MR63); contents are undefined after reset',
          'By holding CKE low for 200 us',
          'By a dedicated RST_n ball on the PoP package',
          'By issuing PREA followed by REFab'
        ],
        chapter: 'init', hard: true,
        explanation: 'The PoP ballout does have an RST_n ball, but it is an eMMC reset signal, not the SDRAM reset. LPDDR3 reset is an MRW to MR63. After it the controller must wait tINIT4, poll DAI or wait tINIT5, redo ZQ init, and rewrite MR1/MR2/MR3/MR11.',
        source: 'JESD209-3C sec 3.3.1' },

      { q: 'After power ramp and CKE goes HIGH, what is the first required step in LPDDR3 initialization?',
        answers: [
          'Issue NOP for at least 200 us (tINIT3), then MRW RESET',
          'Issue MRW RESET immediately',
          'Begin ZQ initialization calibration',
          'Write MR1 and MR2 to configure burst length and latency'
        ],
        chapter: 'init', hard: false,
        explanation: 'The fixed sequence is: supplies valid -> CKE LOW for tINIT1 -> stable clock for tINIT2 -> CKE HIGH -> NOP for tINIT3 = 200 us -> MRW RESET (MR63) -> NOP for tINIT4 = 1 us -> DAI poll or wait tINIT5 -> optional CA training -> ZQ init -> MR1/MR2/MR3/MR11.',
        source: 'JESD209-3C sec 3.3.1' },

      { q: 'Where are read latency (RL) and write latency (WL) programmed in LPDDR3?',
        answers: [
          'MR2: RL in OP3:0, WL set A/B selected by OP6, with pairs such as RL=10/WL=6 (set A) at default speed',
          'MR1, next to the burst-length and nWR fields',
          'MR0, read back as device information',
          'They are fixed by the speed grade and cannot be programmed'
        ],
        chapter: 'init', hard: false,
        explanation: 'MR2 carries the RL/WL pairs. MR1 carries BL (fixed at 8) and nWR. MR0 is read-only device info. The controller chooses the RL/WL pair to match the clock rate.',
        source: 'JESD209-3C sec 3.4.1 (MR2)' },

      { q: 'On an LPDDR3 RD or WR command, what is the function of CA0 on the falling edge?',
        answers: [
          'It is the auto-precharge (AP) flag: CA0f = 1 turns RD into RDA and WR into WRA',
          'It is the least-significant column bit C0',
          'It selects between BL8 and BC4',
          'It carries the bank address LSB'
        ],
        chapter: 'commands', hard: false,
        explanation: 'CA0f is the AP flag. C0 is implied zero and never transmitted; BL8 is fixed; bank selection is on CA7r-CA9r. RDA/WRA are therefore just RD/WR with the AP flag set.',
        source: 'JESD209-3C sec 4.1 (Table 4)' },

      { q: 'On an LPDDR3 PRE command, what does CA4r select?',
        answers: [
          'AB (all-bank): CA4r = 1 precharges all banks; CA4r = 0 precharges the bank on BA0-BA2',
          'Auto-precharge for the preceding RD/WR',
          'The precharge speed mode (fast/typ/slow)',
          'Whether to enter self-refresh instead'
        ],
        chapter: 'commands', hard: false,
        explanation: 'CA4r is the AB flag. When AB = 0 the bank on CA7r-CA9r is precharged (tRPpb). When AB = 1 all banks are precharged (tRPpab, longer on 8-bank devices). Self-refresh and DPD are entered by CKE falling with the REF or PRE code, not by PRE itself.',
        source: 'JESD209-3C sec 4.1 (Table 4)' },

      { q: 'LPDDR3 has no DLL. What does that mean for tDQSCK?',
        answers: [
          'tDQSCK is a wide analog window (2.5 ns to 5.5 ns) that may span multiple clocks; the controller must train its capture',
          'tDQSCK is locked to exactly one clock period',
          'tDQSCK is zero because the strobe is forwarded from CK',
          'tDQSCK only matters during write leveling'
        ],
        chapter: 'timing', hard: true,
        explanation: 'Without a DLL the read strobe appears after a programmable analog delay relative to CK. At fast data rates the max 5.5 ns (5.62 ns derated) can exceed one tCK, so the controller trains capture using the MR32/MR40 DQ calibration patterns and the normal read eye.',
        source: 'JESD209-3C sec 4.4, 11.4 (Table 64)' },

      { q: 'What is the LPDDR3 read-to-write command spacing?',
        answers: [
          'RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL clocks',
          'WL + 1 + BL/2 + RU(tWTR/tCK) clocks',
          'tCCD = 4 clocks',
          'BL/2 + 2 clocks'
        ],
        chapter: 'timing', hard: true,
        explanation: 'RD -> WR = RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL. The tDQSCK term is the LPDDR3 signature. WL + 1 + BL/2 + RU(tWTR/tCK) is the WRITE-to-read direction (tWTR). tCCD covers same-direction column commands.',
        source: 'JESD209-3C sec 4.5' },

      { q: 'What is the LPDDR3 I/O signaling standard?',
        answers: [
          'HSUL_12: 1.2 V high-speed unterminated logic, no VTT termination rail',
          'SSTL_15: 1.5 V stub-series terminated logic',
          'LVSTL: low-voltage series terminated logic at 1.1 V',
          'HSTL_18: 1.8 V high-speed transceiver logic'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'LPDDR3 uses HSUL_12 (1.2 V, unterminated). The CA bus is unterminated; DQ uses asynchronous on-die termination only when enabled. SSTL_15 is desktop DDR3; LVSTL is not the LPDDR3 standard name.',
        source: 'JESD209-3C sec 2.2, 4.12' },

      { q: 'How is the LPDDR3 DQ-bus termination value selected?',
        answers: [
          'By MR11 OP1:0 (RZQ/4, RZQ/2, RZQ/1 or disabled), gated asynchronously by the ODT pin',
          'By MR1 Rtt_NOM and MR2 Rtt_WR like DDR3',
          'Termination is always enabled with a fixed 60 ohm value',
          'By the ODT pin alone; MR11 only enables power-down ODT behavior'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'MR11 OP1:0 selects the ODT value (00 = disabled, 01 = RZQ/4 = 60 ohm, 10 = RZQ/2 = 120 ohm, 11 = RZQ/1 = 240 ohm). The ODT pin turns it on/off asynchronously. OP2 controls whether ODT stays on during power-down. DDR3 splits this across MR1/MR2 with synchronous dynamic ODT; LPDDR3 does not.',
        source: 'JESD209-3C sec 3.4.1 (MR11), 4.12' },

      { q: 'Which statement about LPDDR3 refresh is correct?',
        answers: [
          'Both REFab and REFpb exist; 8 REFpb refresh cycles together equal one REFab of coverage',
          'Only all-bank refresh exists, as in DDR3',
          'REFpb refreshes all banks at once for a shorter tRFC',
          'Refresh is automatic and the controller issues no commands'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'LPDDR3 supports per-bank refresh (REFpb) and all-bank refresh (REFab). REFpb refreshes one bank at a time; the target bank is chosen by an internal round-robin counter. Eight REFpb operations replace one REFab.',
        source: 'JESD209-3C sec 4.8' },

      { q: 'Who selects the target bank of an LPDDR3 REFpb command?',
        answers: [
          'The device\'s internal round-robin counter; the controller must shadow it, re-syncing at reset, self-refresh exit and every REFab',
          'The controller via BA0-BA2 on the CA bus',
          'Always bank 0 first, then incrementing by one each tREFI',
          'The temperature sensor chooses the coolest bank'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'REFpb carries no bank address. The device increments its own counter. The counter re-syncs to bank 0 at reset, at every self-refresh exit, and at every REFab, so the controller must shadow those events.',
        source: 'JESD209-3C sec 4.8' },

      { q: 'What happens to array data when LPDDR3 enters deep power-down (DPD)?',
        answers: [
          'Data is lost; exit requires the full power-up initialization sequence from the NOP wait',
          'Data is retained by the self-refresh engine',
          'Data is retained but refresh obligations are paused',
          'Only the bank currently being refreshed loses data'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'Deep power-down is the lowest-power state. The array is not refreshed, so contents are lost. The minimum stay is tDPD = 500 us, and exit requires the full init sequence (CKE HIGH, NOP 200 us, MRW RESET, etc.).',
        source: 'JESD209-3C sec 4.9' }
    ],

    commandDocs: [
      { cmd: 'ACT', name: 'Activate',
        description: 'Opens row R in bank B - on LPDDR3 the ROW address ' +
                     'is delivered across two edges of the 10-bit CA bus ' +
                     '(CA7r-CA9r select the bank). Spacing: tRCD to the ' +
                     'first column command, tRRD to the next ACT, tFAW ' +
                     'across any four activations, tRC same bank.' },
      { cmd: 'RD', name: 'Read',
        description: 'Bursts 8 words from the open row; the COLUMN address ' +
                     'goes out with this command (C1-C11, C0 implied zero), ' +
                     'and CA0f is the auto-precharge flag. Data returns RL ' +
                     'clocks later plus the uncalibrated tDQSCK window.' },
      { cmd: 'WR', name: 'Write',
        description: 'Bursts 8 words into the open row; column address and ' +
                     'AP flag same as RD. First data is captured WL clocks ' +
                     'after the command. DM masks individual bytes on any ' +
                     'beat.' },
      { cmd: 'RDA', name: 'Read with Auto-Precharge',
        description: 'RD with CA0f = 1: the bank precharges itself once ' +
                     'tRAS and tRTP are met. Re-activation waits tRPpb past ' +
                     'the internal precharge and tRC from the old ACT.' },
      { cmd: 'WRA', name: 'Write with Auto-Precharge',
        description: 'WR with CA0f = 1: the bank precharges itself after ' +
                     'write recovery (WL + BL/2 + tWR past the command). ' +
                     'Re-activation waits tRPpb and tRC.' },
      { cmd: 'PRE', name: 'Precharge',
        description: 'Closes an open row. CA4r = AB selects the target: ' +
                     'AB = 0 precharges the one bank on BA0-BA2 (tRPpb), ' +
                     'AB = 1 precharges all banks (tRPpab, longer). Starts ' +
                     'tRAS after the ACT that opened the row.' },
      { cmd: 'MRR', name: 'Mode Register Read',
        description: 'Reads a mode register back onto DQ0-DQ7 after RL ' +
                     'clocks - how the host learns device info, revision, ' +
                     'temperature/refresh flags and DQ calibration patterns. ' +
                     'Burst length is fixed at 8; only NOP is legal during ' +
                     'the tMRR window.' },
      { cmd: 'MRW', name: 'Mode Register Write',
        description: 'Writes any of the mode registers: MA selects the ' +
                     'register, OP carries the value. All banks must be idle; ' +
                     'tMRW = 10 tCK spacing, tMRD to the next non-MRW ' +
                     'command. Carries BL, RL/WL, nWR, drive strength, ODT, ' +
                     'PASR and training-mode controls.' },
      { cmd: 'REFab/REFpb', name: 'Refresh All Banks / Per Bank',
        description: 'REFab refreshes every bank and needs all banks idle; ' +
                     'REFpb refreshes one bank chosen by the device\'s ' +
                     'round-robin counter. After REFab wait tRFCab; after ' +
                     'REFpb wait tRFCpb for that bank or tRRD for a different ' +
                     'bank. Eight REFpb equal one REFab of refresh coverage.' },
      { cmd: 'SRE/SRX', name: 'Self-Refresh Entry / Exit',
        description: 'Entry: CKE falls while the REF code is on the bus and ' +
                     'all banks are idle; the device refreshes itself with ' +
                     'the clock stopped. Exit: CKE rises asynchronously, then ' +
                     'wait tXSR to commands. At least one refresh must be ' +
                     'issued before re-entering.' },
      { cmd: 'PDE/PDX', name: 'Power-Down Entry / Exit',
        description: 'CKE low with CS_n high parks the device in active or ' +
                     'idle power-down. No refresh occurs, so dwell time is ' +
                     'bounded by the refresh schedule. Exit: CKE rises with ' +
                     'CS_n high; first valid command after tXP. MR11 OP2 ' +
                     'selects whether ODT stays on during power-down.' },
      { cmd: 'DPD', name: 'Deep Power-Down',
        description: 'CKE falls with the PRE code on the bus and all banks ' +
                     'idle. Array contents are lost and every input/output ' +
                     'is shut down for minimum power. Minimum stay tDPD = ' +
                     '500 us; exit requires the full power-up initialization ' +
                     'sequence.' },
      { cmd: 'MRW ZQ/CA/WL', name: 'Calibration and Training Commands',
        description: 'ZQ calibration is an MRW to MR10 (0xFF init, 0xAB ' +
                     'long, 0x56 short, 0xC3 reset). CA training enters via ' +
                     'MR41, remaps via MR48, exits via MR42. Write leveling ' +
                     'is enabled/disabled by MR2[7]. All need all banks idle ' +
                     'and ODT disabled; only NOP is legal during their ' +
                     'windows.' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: [],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
