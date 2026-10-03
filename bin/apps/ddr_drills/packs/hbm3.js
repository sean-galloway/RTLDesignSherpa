// packs/hbm3.js -- HBM3 content pack (JESD238B.01).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/hbm3); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'hbm3',
    name: 'HBM3',
    jedec: {
      doc: 'JESD238B.01',
      note: 'High Bandwidth Memory 3. Most row timings are vendor-datasheet ' +
            'values; the standard defines symbol, unit and constraint.'
    },

    // Simplified drill topology: 2 bank groups of 4 banks, 8 rows, 8 cols,
    // 2 Stack IDs. Real parts: up to 16 channels/stack, each 64 bits split
    // into 2 pseudo channels of 32 bits; 16/32/48/64 banks per channel with
    // 4-16 bank groups; stacks 4-16 dies high.
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
        definition: 'ACT to RD/RDA, same bank. Vendor-datasheet value; 23 nCK ' +
                    'at the 6.4 Gb/s/pin drill speed.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|RDA', scope: 'same_bank' }] },
      { symbol: 'tRCDWR', name: 'Row open to write legal',
        definition: 'ACT to WR/WRA, same bank. Vendor-datasheet value; 23 nCK ' +
                    'at the drill speed.',
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
                    '(RTP >= RU(tRTP/tCK)); PRE on a falling edge adds 0.5 nCK.',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'Last write data to internal precharge legal. MR3 ' +
                    'programs WR >= RU(tWR/tCK); feeds tDAL on WRA.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tPPD', name: 'Precharge-to-precharge packing',
        definition: 'PRE to PRE, same pseudo channel. Fixed at 2 nCK; ' +
                    'PRE/PREab may issue on rising or falling CK edge.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'PRE', scope: 'any' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCDL', name: 'Column command spacing, same bank group',
        definition: 'RD/WR to RD/WR, both banks in one group. ' +
                    'Max(4, 2.5 ns/tCK) nCK; 4 nCK at speed covers a BL8 ' +
                    'burst so same-group commands chain with no bubble.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'same_group' },
                    { from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tCCDS', name: 'Column command spacing, different bank groups',
        definition: 'RD/WR to RD/WR across groups. 2 nCK, so cross-group ' +
                    'commands interleave two per burst duration (BL8 spans ' +
                    '4 nCK).',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'diff_group' }] },
      { symbol: 'tCCDR', name: 'Read spacing across Stack IDs',
        definition: 'RD to RD crossing SIDs (8H and taller). Replaces ' +
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
        definition: 'REFab to next access. 260-450 ns by die density and ' +
                    'stack height; 416 nCK (260 ns) for the 8 Gb/die 8-High ' +
                    'drill example.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'any' }] },
      { symbol: 'tRFCpb', name: 'Per-bank refresh cycle, same bank',
        definition: 'REFpb to next access of that bank. 180-240 ns ' +
                    'representative; exact values TBD/vendor-specific for ' +
                    '8 Gb/die.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REFpb', to: '*', scope: 'same_bank' }] },
      { symbol: 'tRREFD', name: 'Per-bank refresh spacing, different banks',
        definition: 'REFpb to REFpb (or ACT) of a different bank. ' +
                    'MAX(3 x tCK, 8 ns).',
        chapter: 'refresh',
        appliesTo: [{ from: 'REFpb', to: 'REFpb|ACT', scope: 'diff_bank' }] },
      { symbol: 'tREFIpb', name: 'Average per-bank refresh interval',
        definition: 'Average rate of REFpb commands; tREFI / N where N is the ' +
                    'number of banks per channel (16/32/48/64 by stack height).',
        chapter: 'refresh',
        appliesTo: [{ from: 'REFpb', to: 'REFpb', scope: 'any' }] },

      // --- chapter: low-power (reference panel only) -------------------
      { symbol: 'tXS', name: 'Self-refresh exit to valid command',
        definition: 'SRX to any command. MAX(10 x tCK, tRFC(min) + 10 ns). ' +
                    'Panel-only; the drill engine does not emit SRX.',
        chapter: 'low-power',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] },
      { symbol: 'tCPDED', name: 'Command path disable delay',
        definition: 'PDE to internal power-down state. MAX(10 x tCK, 7.5 ns). ' +
                    'Panel-only; the drill engine does not emit PDE.',
        chapter: 'low-power',
        appliesTo: [{ from: 'PDE', to: '*', scope: 'any' }] },
      { symbol: 'tXP', name: 'Power-down exit time',
        definition: 'PDX to next valid command. MAX(10 x tCK, 7.5 ns). ' +
                    'Panel-only; the drill engine does not emit PDX.',
        chapter: 'low-power',
        appliesTo: [{ from: 'PDX', to: '*', scope: 'any' }] }
    ],

    questionBank: [
      { q: 'How wide is the data bus for one HBM3 pseudo channel?',
        answers: [
          '32 DQ bits, with one WDQS/RDQS pair, two ECC bits and two SEV bits',
          '64 DQ bits, the full channel width',
          '16 DQ bits, half of the channel',
          '128 DQ bits, both channels combined'
        ],
        chapter: 'organization', hard: false,
        explanation: 'Each 64-bit HBM3 channel is split into two pseudo channels; DWORD0 (DQ[31:0]) belongs to PC0 and DWORD1 (DQ[63:32]) belongs to PC1. The other widths describe the full channel or non-existent organizations.',
        source: 'JESD238B.01 sec 3.1.2' },

      { q: 'In an HBM3 stack that implements Stack IDs, what role do the SID bits play?',
        answers: [
          'They act as extra bank-address bits for ACT, PREpb, REFpb, RFMpb, RD and WR',
          'They select the row address MSBs',
          'They choose which pseudo channel is active',
          'They replace the column address for BL8 bursts'
        ],
        chapter: 'organization', hard: true,
        explanation: 'SID[1:0] (or SID[0]) behave as additional bank-address bits only for the commands that name a bank. They do not select rows, columns, or pseudo channels; commands other than the listed six ignore SID.',
        source: 'JESD238B.01 sec 3.2 Table 4 note 5' },

      { q: 'At the end of power-ramp, which signals must be driven LOW?',
        answers: [
          'RESET_n and WRST_n, before or when tINIT0 expires',
          'Only RESET_n; WRST_n may stay High-Z',
          'CK_t and CK_c',
          'All R[9:0] and C[7:0] inputs'
        ],
        chapter: 'init', hard: false,
        explanation: 'Both RESET_n and WRST_n must be driven LOW before or at the same time tINIT0 expires, then RESET_n is held LOW for tINIT1. CK_t/CK_c are driven to static LOW/HIGH later, and the command buses are driven to PDE/CNOP after RESET_n rises.',
        source: 'JESD238B.01 sec 4.1' },

      { q: 'When may IEEE 1500 instructions such as SOFT_LANE_REPAIR be used during initialization?',
        answers: [
          'After tINIT3, once WRST_n is driven HIGH',
          'Immediately after power ramp, before RESET_n goes low',
          'Only after all mode registers are programmed',
          'Never; IEEE 1500 is only for mission-mode test'
        ],
        chapter: 'init', hard: true,
        explanation: 'The IEEE 1500 port becomes usable after the precharged power-down interval tINIT3, when WRST_n is driven HIGH. This allows lane repair and channel disable before the normal command sequence resumes.',
        source: 'JESD238B.01 sec 4.4' },

      { q: 'Which command/address bit selects auto-precharge for a read or write?',
        answers: [
          'C3 = 1 enables auto-precharge; C3 = 0 disables it',
          'R2 = 1 enables auto-precharge',
          'The PC bit selects auto-precharge',
          'CA0 is the auto-precharge flag'
        ],
        chapter: 'commands', hard: false,
        explanation: 'The column-bus C3 bit is the auto-precharge flag for both RD/RDA and WR/WRA. R2 is the PREab/PREpb selector on the row bus, and the PC bit selects the pseudo channel, not auto-precharge.',
        source: 'JESD238B.01 Table 31' },

      { q: 'How many CK cycles does an ACTIVATE command occupy on the row bus, and which edge is the timing reference?',
        answers: [
          'One-and-a-half cycles; all row timings reference the second rising CK edge',
          'One cycle; the first rising edge is the reference',
          'Two cycles; the falling edge at the end is the reference',
          'Half a cycle; it shares a cycle with a column command'
        ],
        chapter: 'commands', hard: false,
        explanation: 'ACT spans 1.5 cycles on R[9:0]: bank/PC/SID on the first rising edge, row address across the next edges. The actual bank activation starts on the second rising edge, so tRCD, tRAS, tRC and related timings reference that edge.',
        source: 'JESD238B.01 sec 6.3.2.2' },

      { q: 'What determines the minimum ACT-to-ACT time for the same bank?',
        answers: [
          'tRC = tRAS + tRP: the row must stay open long enough, then the bank must recover',
          'tRCD + tRP: the open and recovery times from either direction',
          '4 x tRRDL: four same-group activates bound the cycle',
          'A vendor value unrelated to tRAS or tRP'
        ],
        chapter: 'timing', hard: false,
        explanation: 'tRC is the same-bank activate cycle and must cover tRAS (earliest legal PRE) plus tRP (precharge to ready). The canonical cycle is ACT -> (tRAS) -> PRE -> (tRP) -> ACT.',
        source: 'JESD238B.01 Table 93' },

      { q: 'Why does tCCDS = 2 nCK let cross-group bursts tile seamlessly for BL8?',
        answers: [
          'A BL8 burst spans 4 nCK; issuing a command every 2 nCK keeps two bursts worth of data in flight across groups',
          'The row bus is reused every 2 nCK across groups',
          'tCCDS is larger than tCCDL, allowing more time for data steering',
          '2 nCK equals one full BL8 burst duration'
        ],
        chapter: 'timing', hard: true,
        explanation: 'BL8 transfers 8 beats at 2 beats per CK, so each burst lasts 4 nCK. With tCCDS = 2 nCK, a second cross-group burst can start halfway through the first, and the spec\'s even/odd re-drive keeps the shared DQ bus continuously occupied.',
        source: 'JESD238B.01 sec 6.3.3.2 Figures 33-35' },

      { q: 'tRTW on HBM3 is best described as...',
        answers: [
          'A system bus-ownership delay computed from RL, WL, BL/4 and strobe offsets',
          'A DRAM array limit between read data and the next write command',
          'A fixed 2 nCK turnaround like tCCDS',
          'The read postamble length of RDQS'
        ],
        chapter: 'timing', hard: true,
        explanation: 'tRTW is NOT a DRAM array limit; it is the time the shared bidirectional DQ/DBI/ECC pins need to change ownership. Table 93 NOTE 18 gives the formula: (RL + BL/4 - WL + 0.5) x tCK + tWDQS2DQ_O(max) - tWDQS2DQ_I(min), rounded up.',
        source: 'JESD238B.01 Table 93 NOTE 18' },

      { q: 'A WRITE followed by a READ to banks in the same bank group is spaced by...',
        answers: [
          'tWTRL; the internal write-to-read delay for same-group banks',
          'tWTRS; cross-group write-to-read spacing',
          'tCCDL; column-to-column spacing covers direction changes',
          'tRTW; this is a read-to-write rule'
        ],
        chapter: 'timing', hard: false,
        explanation: 'Same-group WR -> RD uses tWTRL; different-group uses tWTRS. tCCDL governs same-direction column commands, and tRTW governs RD -> WR, not WR -> RD.',
        source: 'JESD238B.01 Table 6' },

      { q: 'Which data-integrity feature is mandatory on HBM3 behind the link?',
        answers: [
          'Symbol-based on-die ECC that protects each 272-bit data word (256 data bits + 16 metadata bits)',
          'DBIac on every byte of every access',
          'Command/address parity (APAR) with parity latency',
          'CRC on read and write data'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'HBM3 mandates symbol-based on-die ECC behind the link, with SEV-pin severity reporting and ECS scrub. DBIac is mode-register selectable, APAR is optional, and CRC is not a defined HBM3 feature.',
        source: 'JESD238B.01 sec 6.9' },

      { q: 'The internal DBIac state resets to LOW after which events?',
        answers: [
          'RESET_n deassertion, any MRS command, write-to-read bus turnaround, and self-refresh exit',
          'After every read burst and after every write burst',
          'Only at power-up and after a parity error',
          'It never resets; it is a persistent mode register bit'
        ],
        chapter: 'datapath', hard: true,
        explanation: 'The DBIac internal state resets on the listed four events. It does not reset after every individual read or write; instead it seeds the next read from the last data-out.',
        source: 'JESD238B.01 sec 6.2.1.1' },

      { q: 'What is the maximum average refresh interval for REFab, and how much can it stretch?',
        answers: [
          '3.9 us average; up to 8 commands may be postponed, giving a 9 x tREFI absolute bound',
          '7.8 us average; it never stretches',
          '3.9 us average; only 4 commands may be postponed',
          '32 ms total window, like DRAMs that use tREFW'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'tREFI is 3.9 us max. Up to 8 REFab commands may be postponed, so the largest gap between refreshes is 9 x tREFI. The 7.8 us value is the DDR2/DDR3/LPDDR3 high-temperature interval, not the HBM3 base.',
        source: 'JESD238B.01 Table 93 NOTE 23' },

      { q: 'Under per-bank refresh (REFpb), which rule must the controller obey?',
        answers: [
          'Every bank within a Stack ID must be refreshed before any bank of that SID is refreshed a second time',
          'Banks must be refreshed strictly in ascending bank-address order',
          'REFpb never counts against tFAW',
          'tRREFD applies to a second refresh of the same bank'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'REFpb can visit banks in any order, but all banks of an SID must be covered before repeating. REFpb commands count against tFAW like an ACT; tRREFD spaces refreshes to different banks, while tRFCpb spaces refreshes to the same bank.',
        source: 'JESD238B.01 sec 6.3.2.6' },

      { q: 'A part reports RFM = 1 in its IEEE 1500 DEVICE_ID. What must the controller do?',
        answers: [
          'Track a per-bank rolling ACT count (RAA) and issue RFMab/RFMpb before the count reaches RAAMMT',
          'Halve tREFI permanently',
          'Disable REFab and use only REFpb',
          'Nothing; RFM is handled entirely inside the DRAM'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'Refresh Management requires controller bookkeeping: per-bank RAA counters, RAAIMT as the threshold for issuing an RFM command, and RAAMMT as the hard ceiling. RFM does not replace normal REF commands.',
        source: 'JESD238B.01 sec 6.3.2.7' }
    ],

    commandDocs: [
      { cmd: 'ACT', name: 'Activate',
        description: 'Opens row R in bank B (SID + BA select the bank ' +
                     'inside the pseudo channel). Travels on the R[9:0] ' +
                     'row bus over 1.5 cycles - all row timings reference ' +
                     'the second rising edge. Spacing: tRCDRD/tRCDWR to ' +
                     'the first column command, tRRDL/tRRDS to the next ' +
                     'ACT, tFAW across any four, tRC same bank.' },
      { cmd: 'RD', name: 'Read (BL8 fixed)',
        description: 'Bursts 8 words (4 CK of DQ) from the open row on ' +
                     'the C[7:0] column bus; C3 = 0. Same-direction ' +
                     'spacing tCCDL/tCCDS (tCCDR across SIDs), tRTW to a ' +
                     'write, tWTRL/tWTRS from a write.' },
      { cmd: 'RDA', name: 'Read with Auto-Precharge',
        description: 'RD with C3 = 1: the bank precharges itself at ' +
                     'RTP + nCK(MR5) past the burst, once tRAS is met. ' +
                     'The nCK twin must be programmed >= RU(tRTP/tCK).' },
      { cmd: 'WR', name: 'Write (BL8 fixed)',
        description: 'Bursts 8 words into the open row; first data ' +
                     'arrives WL nCK after the command on the column bus, ' +
                     'C3 = 0. On-die ECC check bits are computed and stored ' +
                     'with the data word.' },
      { cmd: 'WRA', name: 'Write with Auto-Precharge',
        description: 'WR with C3 = 1: the bank precharges itself at ' +
                     'WL + 2 + WR(nCK from MR3) past the command. ' +
                     'Re-activation then waits tRP and tRC.' },
      { cmd: 'PRE', name: 'Precharge Per-Bank / All-Bank',
        description: 'PREpb closes the open row of one bank (SID + BA on ' +
                     'the row bus); PREab closes every bank of the PC. ' +
                     'Half-cycle commands legal on rising or falling CK ' +
                     'edge; consecutive PREs pack at tPPD = 2 nCK. Bank ' +
                     'ready again after tRP.' },
      { cmd: 'MRS', name: 'Mode Register Set',
        description: 'Column-bus command writing one of the sixteen mode ' +
                     'registers (register picked by address bits). All ' +
                     'banks idle; spacing tWRMRS/tRDMRS to column ' +
                     'commands and tMOD/tMRD around it. Carries RL, WL, ' +
                     'PL, the nCK twins, DBI/ECC and RFM options.' },
      { cmd: 'REFab', name: 'All-Bank Refresh',
        description: 'One all-bank refresh step; every bank precharged ' +
                     'first, die busy tRFCab. Average rate tREFI (3.9 us ' +
                     'max, shortened past temperature trip points); up ' +
                     'to 8 may be postponed.' },
      { cmd: 'REFpb', name: 'Per-Bank Refresh',
        description: 'Refreshes one bank (SID + BA) for tRFCpb while the ' +
                     'others stay schedulable. Counts against tFAW like ' +
                     'an ACT; tRREFD spaces REFpb to a different bank. ' +
                     'Every bank of an SID must be covered before any ' +
                     'repeat.' },
      { cmd: 'RFMab/RFMpb', name: 'Refresh Management',
        description: 'Extra refreshes the controller owes when a per-' +
                     'bank rolling activate count (RAA) hits RAAIMT: ' +
                     'RFMab all banks, RFMpb one bank. Timing mirrors ' +
                     'REFab/REFpb. Mandatory on parts reporting RFM = 1.' },
      { cmd: 'PDE/PDX', name: 'Power-Down Entry / Exit',
        description: 'PDE (R[3:0] = PDE pattern) parks the pseudo channel ' +
                     'precharged or active. PDE and CNOP must be held for ' +
                     'tCPDED; CK may stop after tCKPDE. PDX (R0 HIGH with ' +
                     'CNOP) exits; commands legal after tXP.' },
      { cmd: 'SRE/SRX', name: 'Self-Refresh Entry / Exit',
        description: 'Row-bus commands: SRE enters self refresh when all ' +
                     'banks of both PCs are precharged, preserving data ' +
                     'without external CK. R0 = LOW holds the state. SRX ' +
                     'exits; commands legal after tXS, MRS after tXSMRS.' },
      { cmd: 'RNOP/CNOP', name: 'Row/Column No-Operation',
        description: 'Filler on the two independent command buses - ' +
                     'RNOP parks the row bus, CNOP parks the column ' +
                     'bus, so one bus can idle while the other works ' +
                     '(e.g. ACT on R with NOP on C the same cycle).' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: ['sid', 'cross_group'],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
