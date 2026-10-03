// packs/ddr5.js -- DDR5 content pack (JESD79-5B).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/ddr5); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
//
// DDR5 keeps bank groups and adds two independent 32-bit sub-channels per
// DIMM. The drill model uses 4 BG x 2 banks; real x16 parts have 4 BG x 4
// banks per sub-channel (16 banks), and x4/x8 parts have 8 BG x 4 banks
// (32 banks).
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'ddr5',
    name: 'DDR5',
    jedec: {
      doc: 'JESD79-5B',
      note: 'DDR5 SDRAM. Two independent 32-bit sub-channels per DIMM; ' +
            'bank-group short/long timing splits; BL16 with BC8 OTF and ' +
            'optional BL32 (x4); on-die ECC; no DBI and no CA parity; ' +
            'link-level write/read CRC; 4-tap DFE; command-based power ' +
            'states (no CKE); MRW/MRR; MPC training; RFM and REFsb; ' +
            '1.1 V VDD/VDDQ and 1.8 V VPP.'
    },

    // Simplified drill topology: 4 bank groups of 2 banks, 8 rows, 8 cols.
    // Real x16 parts: 4 groups of 4 banks per 32-bit sub-channel (16 banks).
    // Real x4/x8 parts: 8 groups of 4 banks per sub-channel (32 banks).
    topology: {
      hasBankGroups: true,
      groups: 4,
      banksPerGroup: 2,
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
                    'sense amps before a column command is legal; 15 ns ' +
                    '(24 nCK) at DDR5-3200AN.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tRP', name: 'Precharge recovery',
        definition: 'PRE to ACT, same bank. Sense amps and bitlines restore ' +
                    'before the bank may re-open; 15 ns (24 nCK) at ' +
                    'DDR5-3200AN, bin-matched to tRCD.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRAS', name: 'Minimum row-open time',
        definition: 'ACT to PRE, same bank. Cell data must be restored ' +
                    'before the row closes; 32 ns (52 nCK) at DDR5-3200AN.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRC', name: 'Full row cycle',
        definition: 'ACT to ACT, same bank; equals tRAS + tRP (47 ns, 76 nCK ' +
                    'at DDR5-3200AN) by construction.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRRDS', name: 'Activate spacing, different bank groups',
        definition: 'ACT to ACT across bank groups. 8 nCK (all bins); the ' +
                    'fast path that lets interleaved activates keep pace.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_group' }] },
      { symbol: 'tRRDL', name: 'Activate spacing, same bank group',
        definition: 'ACT to ACT, different banks in one group. max(8 nCK, ' +
                    '5 ns) at DDR5-3200AN; same-group activates share local ' +
                    'row resources.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_group' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'No more than 4 ACT commands in any rolling tFAW-wide ' +
                    'window. max(32 nCK, 20 ns) for 1K page, max(40 nCK, ' +
                    '25 ns) for 2K page at DDR5-3200AN; independent of bank ' +
                    'group.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRTP', name: 'Read to precharge',
        definition: 'RD/RDA to PRE, same bank. The internal analog read must ' +
                    'finish before the row closes; max(12 nCK, 7.5 ns).',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'WR/WRA to PRE, same bank. Last write data must be ' +
                    'committed to cells before precharge; 30 ns (48 nCK) at ' +
                    'DDR5-3200AN, programmed via MR6.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tPPD', name: 'Precharge-to-precharge delay',
        definition: 'PRE to PRE spacing, any banks. 2 nCK minimum between any ' +
                    'precharge commands.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'PRE', scope: 'any' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCDS', name: 'Column spacing, different bank groups',
        definition: 'Same-direction column command to column command across ' +
                    'groups. 8 nCK at BL16; two interleaved groups can keep ' +
                    'the DQ bus busy.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'diff_group' }] },
      { symbol: 'tCCDL', name: 'Column spacing, same bank group',
        definition: 'Same-direction column command to column command inside ' +
                    'one group. max(8 nCK, 5 ns) at DDR5-3200AN; a single ' +
                    'group cannot saturate the bus no matter how many banks ' +
                    'it has.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'same_group' },
                    { from: 'RD|WR|RDA|WRA', to: 'RD|WR|RDA|WRA', scope: 'same_bank' }] },
      { symbol: 'tCCD_L_WR', name: 'Write-to-write spacing, same bank, RMW',
        definition: 'WR/WRA to WR/WRA to the same bank; the second write ' +
                    'needs an internal read-modify-write. max(32 nCK, 20 ns) ' +
                    'at DDR5-3200AN.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'WR|WRA', scope: 'same_bank' }] },
      { symbol: 'tCCD_L_WR2', name: 'Write-to-write spacing, same group, no RMW',
        definition: 'WR/WRA to WR/WRA inside one bank group when the second ' +
                    'write does not need an internal read-modify-write. ' +
                    'max(16 nCK, 10 ns) at DDR5-3200AN.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'WR|WRA', scope: 'same_group' }] },
      { symbol: 'tRTW', name: 'Read-to-write turnaround',
        definition: 'Book symbol - JESD79-5B names the underlying rule ' +
                    'tCCD_L_RTW / tCCD_S_RTW, not bare tRTW. The read burst ' +
                    'and postamble must clear before the write preamble; ' +
                    'command gap = CL - CWL + RBL/2 + 2nCK - (Read DQS ' +
                    'offset) + (tRPST - 0.5nCK) + tWPRE (15 nCK in the drill ' +
                    'model).',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tWTRS', name: 'Write-to-read, different bank groups',
        definition: 'Last write data to internal read across bank groups. ' +
                    'CWL + WBL/2 + max(4 nCK, 2.5 ns); 34 nCK in the drill ' +
                    'model.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'diff_group' }] },
      { symbol: 'tWTRL', name: 'Write-to-read, same bank group',
        definition: 'Last write data to internal read inside one group. ' +
                    'CWL + WBL/2 + max(16 nCK, 10 ns); 46 nCK in the drill ' +
                    'model.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'same_group' },
                    { from: 'WR|WRA', to: 'RD|RDA', scope: 'same_bank' }] },
      { symbol: 'tCCD_WTRA', name: 'Write-to-read with auto-precharge, same bank',
        definition: 'WR/WRA to RD/RDA on the same bank when the write used ' +
                    'auto-precharge. CWL + WBL/2 + tWR - tRTP. Same-bank ' +
                    'access only.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'same_bank' }] },

      // --- chapter: init (reference panel; MRW/MRR/MPC are not engine cmds) ---
      { symbol: 'tMRW', name: 'Mode-register write command period',
        definition: 'MRW to MRW. max(5 ns, 8 nCK). Panel-only: the drill ' +
                    'engine does not emit MRW commands.',
        chapter: 'init',
        appliesTo: [{ from: 'MRW', to: 'MRW', scope: 'any' }] },
      { symbol: 'tMRD', name: 'Mode-register command delay',
        definition: 'MRW/MRR to any non-mode-register command. max(14 ns, ' +
                    '16 nCK). Panel-only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRW', to: '*', scope: 'any' }] },
      { symbol: 'tDLLK', name: 'DLL lock time',
        definition: 'DLL reset to a command that needs a locked DLL, such as ' +
                    'RD. Programmed via MPC Configure into MR13; 1024 nCK at ' +
                    'DDR5-3200. Panel-only.',
        chapter: 'init',
        appliesTo: [{ from: 'MRW', to: 'RD|RDA', scope: 'any' }] },

      // --- chapter: refresh (reference panel; REF/SRX are engine-only) -
      { symbol: 'tREFI1', name: 'Average refresh interval, normal mode',
        definition: 'REFab to REFab average in normal 1x mode. 3.9 us at ' +
                    'normal temperature, halved above 85 C; FGR 2x uses ' +
                    'tREFI2 = tREFI1/2. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFC1', name: 'Refresh cycle time, normal mode',
        definition: 'REFab/RFMab to next command in normal 1x mode. 195/295/' +
                    '410 ns by density (8/16/24-32 Gb). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'any' }] },
      { symbol: 'tRFC2', name: 'Refresh cycle time, fine granularity mode',
        definition: 'REFab/RFMab to next command in FGR 2x mode. 130/160/220 ' +
                    'ns by density (8/16/24-32 Gb). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'any' }] },
      { symbol: 'tRFCsb', name: 'Refresh cycle time, same bank',
        definition: 'REFsb/RFMsb to next command affecting the refreshed bank. ' +
                    '115/130/190 ns by density (8/16/24-32 Gb). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: '*', scope: 'any' }] },
      { symbol: 'tXS', name: 'Self-refresh exit to non-DLL commands',
        definition: 'SRX to ACT, PRE, MRW, MRR, or REF. tRFC1(min); commands ' +
                    'that need a locked DLL (RD/WR/MRR) wait the additional ' +
                    'tXS_DLL = tDLLK. Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: 'ACT|PRE|MRW|MRR|REF', scope: 'any' }] },
      { symbol: 'tXP', name: 'Power-down exit',
        definition: 'PDX to any valid command when the DLL was kept on. ' +
                    'max(7.5 ns, 8 nCK). Panel-only.',
        chapter: 'refresh',
        appliesTo: [{ from: 'SRX', to: '*', scope: 'any' }] }
    ],

    questionBank: [
      { q: 'What is the headline organization change that distinguishes DDR5 from DDR4?',
        answers: [
          'Two independent 32-bit sub-channels per DIMM, more bank groups, and a 16n prefetch',
          'The prefetch stays at 8n and the channel stays 64 bits wide',
          'The supply voltage drops from 1.2 V to 0.9 V',
          'CKE still controls power-down entry and exit'
        ],
        chapter: 'organization', hard: false,
        explanation: 'DDR5 splits each DIMM into two independent 32-bit sub-channels and moves to a 16n prefetch. VDD is 1.1 V, not 0.9 V, and DDR5 has no CKE pin; power-down is command-based via PDE/PDX.',
        source: 'JESD79-5B sec 2.6, 2.7' },

      { q: 'How many independent 32-bit sub-channels does a DDR5 DIMM present to the controller?',
        answers: [
          'Two sub-channels, each with its own CA bus and 32-bit DQ bus',
          'One 64-bit channel like DDR4',
          'Four 16-bit channels',
          'Eight 8-bit channels'
        ],
        chapter: 'organization', hard: false,
        explanation: 'A DDR5 DIMM has two independent 32-bit sub-channels. Each has its own device set, command/address bus, and data bus; the controller schedules them independently.',
        source: 'JESD79-5B sec 2.6' },

      { q: 'On a DDR5 RD, WR, or WRA command, what does CA10 = L select?',
        answers: [
          'Auto-precharge: the bank closes itself after the burst (RDA/WRA)',
          'Burst-chop / alternate burst length (BC8 or BL32)',
          'The bank group address',
          'Write-partial / data-mask flag'
        ],
        chapter: 'commands', hard: false,
        explanation: 'In DDR5 the auto-precharge flag is active-low on CA10 of the second command cycle. CA5 = L selects the alternate burst length programmed by MR0 OP[1:0], and CA11 carries WR_Partial. Bank groups are selected by BG pins.',
        source: 'JESD79-5B sec 4.1' },

      { q: 'On a DDR5 column command, what does CA5 = L mean when BC8 on-the-fly is enabled?',
        answers: [
          'Select the alternate burst length programmed in MR0 OP[1:0] (BC8 OTF, BL32 fixed, or BL32 OTF)',
          'Select auto-precharge',
          'Select the bank group',
          'Force BL16 regardless of MR0'
        ],
        chapter: 'commands', hard: false,
        explanation: 'CA5 is the BL* flag. CA5 = L chooses the alternate burst length defined by MR0 OP[1:0] (01B = BC8 OTF, 10B = BL32 fixed, 11B = BL32 OTF); CA5 = H uses the default BL16. Auto-precharge is CA10, and bank groups are BG pins.',
        source: 'JESD79-5B sec 4.1' },

      { q: 'Which of the following DDR5 commands are issued as two-cycle commands on the CA bus?',
        answers: [
          'ACT, RD, WR, RDA, WRA, MRW, MRR, and WRP',
          'All commands including REFab and PREab',
          'Only ACT',
          'Only RD and WR'
        ],
        chapter: 'commands', hard: true,
        explanation: 'ACT, RD, WR, RDA, WRA, MRW, MRR, and WRP are two-cycle commands. REFab, PREab, MPC, NOP, PDE, etc. are one-cycle commands. CA1 = L marks the first cycle of a two-cycle command.',
        source: 'JESD79-5B sec 4.1' },

      { q: 'During DDR5 initialization, what is the correct early command sequence after reset exit and NOPs?',
        answers: [
          'MPC Configure (MR13), MPC DLL Reset, MPC ZQCal Start, MPC ZQCal Latch, then training',
          'MRW to MR0 to set CL and burst length first',
          'Issue an all-bank REF command to wake the array',
          'Begin CS/CA training before configuring tCCD_L and tDLLK'
        ],
        chapter: 'init', hard: true,
        explanation: 'The fixed early sequence is MPC Configure (loads tCCD_L, tCCD_L_WR, tCCD_L_WR2, tDLLK into MR13), MPC DLL Reset, then ZQCal Start/Latch, followed by write leveling, CS/CA training, and Vref training.',
        source: 'JESD79-5B sec 3.3.1' },

      { q: 'How are the tCCD_L and tDLLK values programmed in DDR5?',
        answers: [
          'An MPC Configure command writes them into MR13, which is read-only via MRW',
          'A direct MRW to MR13 sets them',
          'They are hardcoded at power-up and cannot change',
          'They are selected by MR0 OP[1:0] along with burst length'
        ],
        chapter: 'init', hard: false,
        explanation: 'MR13 is loaded by the MPC Configure command and is read-only via MRW. It holds the programmed values for tCCD_L, tCCD_L_WR, tCCD_L_WR2, and tDLLK.',
        source: 'JESD79-5B sec 3.5.15' },

      { q: 'Two consecutive same-direction column commands to the SAME bank group are spaced by...',
        answers: [
          'tCCDL, which is longer than tCCDS and prevents a single group from saturating the bus',
          'tCCDS, because same-group commands are the fast path',
          'tRRDL, the activate spacing',
          'tFAW, the four-activate window'
        ],
        chapter: 'timing', hard: true,
        explanation: 'Same-group column spacing is tCCDL (max(8 nCK, 5 ns) at DDR5-3200AN); cross-group spacing is tCCDS (8 nCK). tRRDL governs activates, not column commands, and tFAW is a rolling activate window.',
        source: 'JESD79-5B sec 4.7' },

      { q: 'A write followed by a read to a DIFFERENT bank group is governed by...',
        answers: [
          'tWTRS = CWL + WBL/2 + max(4 nCK, 2.5 ns); 34 nCK in the drill model',
          'tWTRL, the same-group write-to-read parameter',
          'tCCDS, the column-to-column spacing',
          'tRTW, the read-to-write turnaround'
        ],
        chapter: 'timing', hard: true,
        explanation: 'WR -> RD across bank groups uses tWTRS. Same-group WR -> RD uses the larger tWTRL. tRTW is RD -> WR, and tCCDS is same-direction column spacing.',
        source: 'JESD79-5B sec 4.8' },

      { q: 'Which formula gives the DDR5 read-to-write command spacing (book symbol tRTW)?',
        answers: [
          'CL - CWL + RBL/2 + 2nCK - (Read DQS offset) + (tRPST - 0.5nCK) + tWPRE',
          'CWL + WBL/2 + max(16 nCK, 10 ns)',
          'tCCDS + tCCDL',
          'BL/2 + 1'
        ],
        chapter: 'timing', hard: true,
        explanation: 'JESD79-5B names the rule tCCD_L_RTW / tCCD_S_RTW, not bare tRTW. The formula is CL - CWL + RBL/2 + 2nCK - (Read DQS offset) + (tRPST - 0.5nCK) + tWPRE. The second choice is tWTRL, and the other two are oversimplifications.',
        source: 'JESD79-5B sec 4.8' },

      { q: 'What is true about DDR5 on-die ECC?',
        answers: [
          'It is mandatory, invisible to the host, and corrects single-bit errors (128 data + 8 check bits)',
          'It is optional and visible to the controller as extra ECC DQ bits',
          'DDR5 does not define on-die ECC',
          'It is the same function as link-level write CRC'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'On-die ECC is mandatory in DDR5 and is invisible to the host; the DRAM stores extra check bits and corrects single-bit errors internally. Link-level CRC protects the DQ bus during transfer and is a separate feature.',
        source: 'JESD79-5B sec 4.36' },

      { q: 'Which statement about DDR5 DBI and CRC is correct?',
        answers: [
          'DDR5 has no DBI; link data integrity relies on write CRC and optional read CRC instead',
          'Read DBI is enabled in MR5 like DDR4',
          'Write DBI and DM can be enabled together',
          'DBI is mandatory for x16 devices'
        ],
        chapter: 'datapath', hard: false,
        explanation: 'DDR5 does not define data-bus inversion. Write CRC and optional read CRC use the same ATM-8 HEC polynomial as DDR4. DM is enabled separately in MR5 and causes an internal read-modify-write when any byte is masked.',
        source: 'JESD79-5B sec 4.38' },

      { q: 'Which statement about DDR5 refresh modes is true?',
        answers: [
          'Normal (tREFI1/tRFC1), FGR 2x (tREFI2/tRFC2), and same-bank refresh (tREFIsb/tRFCsb) are all defined',
          'Only all-bank refresh is supported',
          'Per-bank refresh like LPDDR3 is the default',
          'FGR mode doubles the tREFI interval'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'DDR5 supports normal all-bank refresh, fine-granularity refresh (FGR 2x with tREFI2 = tREFI1/2 and shorter tRFC2), and same-bank refresh (REFsb with tRFCsb). FGR halves the interval, not doubles it.',
        source: 'JESD79-5B sec 4.13' },

      { q: 'What is the purpose of Refresh Management (RFM) in DDR5?',
        answers: [
          'It provides extra internal refresh time when high activate activity threatens row reliability',
          'It replaces normal REF commands entirely',
          'It enables per-bank refresh scheduling',
          'It calibrates output driver impedance'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'RFMab/RFMsb are bonus refresh commands used when MR58 OP[0] indicates RFM is required. A rolling accumulated ACT count (RAA) increments per activate; RFM/REF decrements it. It does not replace normal refresh or enable per-bank refresh.',
        source: 'JESD79-5B sec 4.13' },

      { q: 'Which statement about DDR5 BL32 mode is correct?',
        answers: [
          'BL32 is optional and supported only on x4 devices',
          'BL32 is the default burst length',
          'BL32 is supported on x4, x8, and x16 organizations',
          'DDR5 does not define a BL32 mode'
        ],
        chapter: 'organization', hard: false,
        explanation: 'BL16 is the default burst length. BL32 (fixed or on-the-fly) is optional and only for x4 devices; x8 and x16 devices support BL16 and BC8 OTF.',
        source: 'JESD79-5B sec 4.2' }
    ],

    commandDocs: [
      { cmd: 'ACT', name: 'Bank Activate',
        description: 'Opens row R in bank B selected by BG and BA. The row ' +
                     'address is split across both cycles of the command. ' +
                     'Spacing: tRCD to the first RD/WR, tRRDS cross-group, ' +
                     'tRRDL same-group, tFAW across any four activates, tRC ' +
                     'same bank.' },
      { cmd: 'PRE', name: 'Precharge (one bank, all banks, or same bank)',
        description: 'Closes the open row and restores data. PREpb closes the ' +
                     'bank selected by BG/BA; PREab closes all banks; PREsb ' +
                     'closes the addressed bank in every group. tPPD applies ' +
                     'between any precharges, and tRP before the next ACT.' },
      { cmd: 'RD', name: 'Read',
        description: 'Bursts BL16, BC8, or optional BL32 words from the open ' +
                     'row starting at the issued column; data appears RL = CL ' +
                     'clocks later. CA10 = L selects auto-precharge on RDA. ' +
                     'CA5 = L selects the alternate burst length when OTF is ' +
                     'enabled. Cross-group spacing tCCDS; same-group tCCDL; ' +
                     'tRTW to a write.' },
      { cmd: 'RDA', name: 'Read with Auto-Precharge',
        description: 'RD with CA10 = L on cycle 2: the bank precharges itself ' +
                     'once tRAS and tRTP are met. Re-activation waits tRP from ' +
                     'the internal precharge and tRC from the old ACT.' },
      { cmd: 'WR', name: 'Write',
        description: 'Bursts BL16, BC8, or optional BL32 words into the open ' +
                     'row; first data is captured CWL = CL - 2 clocks after ' +
                     'the command. CA10 = L selects auto-precharge on WRA. ' +
                     'CA5 = L selects alternate burst length when OTF is ' +
                     'enabled. CA11 = WR_Partial must be low when any DM_n ' +
                     'masks data, forcing an internal RMW.' },
      { cmd: 'WRA', name: 'Write with Auto-Precharge',
        description: 'WR with CA10 = L on cycle 2: the bank precharges itself ' +
                     'after write recovery. Next ACT waits WL + BL/2 + nWR + ' +
                     'tRP (and tRC). The write may still need an internal RMW ' +
                     'if any byte is masked.' },
      { cmd: 'MRW', name: 'Mode Register Write',
        description: 'Writes one of MR0-MR255 with an 8-bit opcode. All banks ' +
                     'must be idle. MRW to read-only registers has no effect. ' +
                     'tMRW between MRW commands, tMRD before any non-MRW/MRR ' +
                     'command. Carries CL, CWL, BL, preamble/postamble, DM, ' +
                     'TDQS, refresh mode, ECS, CRC, and training controls.' },
      { cmd: 'MRR', name: 'Mode Register Read',
        description: 'Reads one of MR0-MR255; the 8-bit OP code returns on ' +
                     'BL8-BL15 of a BL16 burst with odd DQ bits inverted. All ' +
                     'banks idle. tMRD before the next non-MRW/MRR command.' },
      { cmd: 'REFab/REFsb/RFMab/RFMsb', name: 'Refresh and Refresh Management',
        description: 'REFab refreshes all banks; REFsb refreshes the addressed ' +
                     'bank in every group. RFMab/RFMsb provide extra internal ' +
                     'refresh time when RFM is required (MR58 OP[0] = 1). All ' +
                     'banks must be idle for REFab/RFMab; the addressed bank ' +
                     'must be idle for REFsb/RFMsb. Wait tRFC1/tRFC2/tRFCsb ' +
                     'respectively; average rate tREFI1/tREFI2/tREFIsb.' },
      { cmd: 'MPC', name: 'Multi-Purpose Command',
        description: 'Carries one of many opcodes for calibration and ' +
                     'training: ZQCal Start/Latch, DLL reset, Configure ' +
                     '(MR13), DQS oscillator, RTT settings, read training ' +
                     'pattern, ECS, etc. Some MPC commands need trailing DES ' +
                     'cycles; prior to CS/CA training completion MPC uses ' +
                     'multi-cycle CS assertion unless MR2 OP[4] = 1.' },
      { cmd: 'SRE/SRX', name: 'Self-Refresh Entry / Exit',
        description: 'Entry: SRE with all banks idle and no data bursts. Exit: ' +
                     'any valid command after CKE-less self-refresh. Wait tXS ' +
                     '= tRFC1 to non-DLL commands and tXS_DLL = tDLLK to ' +
                     'RD/WR/MRR. After exit, at least one extra refresh is ' +
                     'required before re-entry.' },
      { cmd: 'PDE/PDX', name: 'Power-Down Entry / Exit',
        description: 'PDE enters power-down command-based (DDR5 has no CKE ' +
                     'pin); PDX is a NOP-like command that exits. PDE is ' +
                     'illegal during RD/WR/MRR/MRW and some training. Exit to ' +
                     'any valid command waits tXP. Stay bounded by refresh ' +
                     'requirements.' },
      { cmd: 'NOP/DES', name: 'No Operation / Deselect',
        description: 'Bus fillers: NOP keeps CS_n low, DES raises CS_n. ' +
                     'Neither changes state. Required through mode-register, ' +
                     'self-refresh-exit, power-down, and gear-down windows.' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: [],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
