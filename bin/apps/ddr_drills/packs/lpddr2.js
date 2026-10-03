// packs/lpddr2.js -- LPDDR2 content pack (JESD209-2F).
// Content paraphrased from the condensed study-notes book
// (cold_storage/MemorySpecs/docs/lpddr2); every question cites the spec
// section the book cites. Dual-environment header: same bytes run as a
// browser <script> tag and under node require() in the test harness.
//
// LPDDR2 is a FLAT topology: no bank groups, no Stack IDs. Scopes used
// in appliesTo are therefore same_bank / diff_bank / any only.
// tCCD is modeled same-direction only, matching the book's gap sheet -
// direction changes use the formula-based turnaround rules, which always
// dominate tCCD there. tRPab (all-bank precharge) is reference-panel
// only: the drill model's PRE is per-bank, so it uses tRPpb.
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  DDRD.registerPack({
    id: 'lpddr2',
    name: 'LPDDR2',
    jedec: {
      doc: 'JESD209-2F',
      note: 'Low Power DDR2. CA-bus command interface, no DLL and no ODT, ' +
            'turnarounds expressed as formulas over RL/WL/BL/tDQSCK. tRTW ' +
            'is a book symbol: the spec gives the read-to-write rule as an ' +
            'unnamed formula.'
    },

    // Simplified drill topology: 8 banks, 8 rows, 8 cols, flat. Real
    // parts: 4 banks (512 Mb and below) or 8 banks (1 Gb+ S4), x8/x16/x32.
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
        definition: 'ACT to PRE, same bank. 42 ns, min 3 tCK; max 70 us.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tRPpb', name: 'Precharge time, one bank',
        definition: 'PRE (single bank) to ACT of that bank. 15/18/24 ns, ' +
                    'min 3 tCK.',
        chapter: 'core',
        appliesTo: [{ from: 'PRE', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRPab', name: 'Precharge time, all banks',
        definition: 'PRE-all to ACT of any bank. Equals tRPpb on 4-bank ' +
                    'parts; LONGER on 8-bank parts (18/21/27 ns). Panel ' +
                    'only - the drill model\'s PRE is per-bank.',
        chapter: 'core',
        appliesTo: [{ from: 'PREA', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRC', name: 'Row cycle',
        definition: 'ACT to ACT, same bank: tRAS + tRPpb (or tRAS + tRPab ' +
                    'after a PRE-all).',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'same_bank' }] },
      { symbol: 'tRRD', name: 'Activate spacing, different banks',
        definition: 'ACT to ACT, different banks. 10 ns, min 2 tCK. ' +
                    'A REFpb counts as an activation for tFAW.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'diff_bank' }] },
      { symbol: 'tFAW', name: 'Four-activate rolling window',
        definition: 'At most 4 ACTs in any rolling window (8-bank parts ' +
                    'only). 50 ns, min 8 tCK.',
        chapter: 'core',
        appliesTo: [{ from: 'ACT', to: 'ACT', scope: 'any' }] },
      { symbol: 'tRTP', name: 'Read to precharge',
        definition: 'RD to PRE, same bank: last-prefetch analog delay. ' +
                    '7.5 ns, min 2 tCK; clock counting starts BL/2 - 2 ' +
                    'after the RD on S4.',
        chapter: 'core',
        appliesTo: [{ from: 'RD|RDA', to: 'PRE', scope: 'same_bank' }] },
      { symbol: 'tWR', name: 'Write recovery',
        definition: 'Last write data to PRE, same bank. 15 ns, min 3 ' +
                    'tCK; the MR1 nWR field carries RU(tWR/tCK) for ' +
                    'auto-precharge.',
        chapter: 'core',
        appliesTo: [{ from: 'WR|WRA', to: 'PRE', scope: 'same_bank' }] },

      // --- chapter: turnaround (column/bus timings) --------------------
      { symbol: 'tCCD', name: 'Column-to-column spacing',
        definition: 'Same-direction column commands, any banks: 2 tCK ' +
                    'on S4 (4n prefetch), 1 tCK on S2. Direction changes ' +
                    'use the turnaround formulas instead.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'RD|RDA', scope: 'any' },
                    { from: 'WR|WRA', to: 'WR|WRA', scope: 'any' }] },
      { symbol: 'tWTR', name: 'Write-to-read delay',
        definition: 'End of write burst data to RD. 7.5 ns (10 ns on ' +
                    'slow grades), min 2 tCK; command form ' +
                    'WL + 1 + BL/2 + RU(tWTR/tCK).',
        chapter: 'turnaround',
        appliesTo: [{ from: 'WR|WRA', to: 'RD|RDA', scope: 'any' }] },
      { symbol: 'tRTW', name: 'Read-to-write turnaround',
        definition: 'Book symbol - JESD209-2F gives the rule unnamed, ' +
                    'as a formula: RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - ' +
                    'WL clocks. No DLL, so the multi-clock tDQSCK must ' +
                    'be absorbed before write data may drive.',
        chapter: 'turnaround',
        appliesTo: [{ from: 'RD|RDA', to: 'WR|WRA', scope: 'any' }] },

      // --- chapter: refresh (reference panel; the drill engine does ----
      // --- not emit REF commands, so these never match a question) -----
      { symbol: 'tREFI', name: 'Average refresh interval (reference)',
        definition: 'tREFW / R: 15.6 / 7.8 / 3.9 us by density. A ' +
                    'REFERENCE only - the real contract is R refreshes ' +
                    'in every rolling tREFW (32 ms), any pattern.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF', scope: 'any' }] },
      { symbol: 'tRFCab', name: 'All-bank refresh cycle',
        definition: 'REFab to next command, device busy. 90 ns (<=1 ' +
                    'Gb), 130 ns (2-4 Gb), 210 ns (6-8 Gb).',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'REF|ACT', scope: 'any' }] },
      { symbol: 'tRFCpb', name: 'Per-bank refresh cycle',
        definition: 'REFpb to ACT of the same bank or the next REF. ' +
                    '60 ns (<=4 Gb). Only the target bank is busy; a ' +
                    'different bank needs just tRRD. 8 REFpb replace ' +
                    'one REFab.',
        chapter: 'refresh',
        appliesTo: [{ from: 'REF', to: 'ACT', scope: 'same_bank' }] }
    ],

    questionBank: [
      { q: 'How do LPDDR2-S4 and LPDDR2-S2 differ at the prefetch level?',
        answers: [
          'S4 has a 4n prefetch (minimum burst occupies 2 clocks, tCCD = 2); S2 has 2n (1-clock bursts, tCCD = 1)',
          'S4 is single-data-rate, S2 is dual-data-rate',
          'S2 has the deeper prefetch and the wider tCCD',
          'They differ only in voltage'
        ],
        chapter: 'organization', hard: false,
        explanation: 'S4 fetches 4 words per DQ internally and delivers 2 per clock (DDR), so a minimum burst occupies 2 clocks and tCCD = 2. S2 halves that: 2n prefetch, 1-clock minimum bursts, tCCD = 1.',
        source: 'JESD209-2F sec 3' },

      { q: 'What is unusual about column address bit C0 on the LPDDR2 CA bus?',
        answers: [
          'It is never transmitted - C0 is implied zero, so bus column addresses start at C1',
          'It selects the bank group',
          'It toggles auto-precharge',
          'It is the DM mask bit'
        ],
        chapter: 'organization', hard: true,
        explanation: 'The CA bus never carries C0; it is implied zero. (The other addressing trap: 6 Gb parts have no memory where R13 and R14 are both high.)',
        source: 'JESD209-2F sec 2.13 (Table 3)' },

      { q: 'A dual-channel LPDDR2 PoP package contains...',
        answers: [
          'Two fully independent channels, each with its own CA bus, clock, CKE and CS_n - nothing shared but the package',
          'Two channels sharing one CA bus to save pins',
          'One channel with two chip selects',
          'A primary channel and a refresh-only channel'
        ],
        chapter: 'organization', hard: false,
        explanation: 'Multi-channel LPDDR2 is a package-level construct: each channel is a complete independent device with its own CA bus, CK, CKE and CS_n. The entire protocol is per-channel.',
        source: 'JESD209-2F sec 2.13' },

      { q: 'Where are read latency (RL) and write latency (WL) programmed?',
        answers: [
          'MR2 - one field pair, set by speed grade (e.g. RL=8/WL=4 at LPDDR2-1066, RL=3/WL=1 at 466 and slower)',
          'MR1, next to the burst length',
          'MR4, with the temperature sensor',
          'They are hard-wired per part'
        ],
        chapter: 'init', hard: false,
        explanation: 'MR2 carries RL and WL, chosen by speed grade: 8/4 at 1066 down to 3/1 at 466 and slower. (MR1 is burst length and nWR; MR4 is the temperature/refresh-rate readout.)',
        source: 'JESD209-2F sec 5.4 (MR2)' },

      { q: 'LPDDR2 has no DLL. What does that mean for tDQSCK?',
        answers: [
          'tDQSCK is an analog delay (2500-5500 ps) that may span MULTIPLE clocks - the controller must absorb it with a trained capture, not a fixed clock count',
          'tDQSCK is always exactly one clock',
          'The strobe is forwarded from CK, so tDQSCK is zero',
          'tDQSCK only matters above 85 C'
        ],
        chapter: 'timing', hard: true,
        explanation: 'Without a DLL the read strobe appears tDQSCK after the clock edge, and at fast grades that delay exceeds a clock. First data = RL*tCK + tDQSCK + tDQSQ after the RD command.',
        source: 'JESD209-2F sec 5.5' },

      { q: 'When is tRPab (all-bank precharge) LONGER than tRPpb (per-bank)?',
        answers: [
          'On 8-bank devices only - it keeps an all-bank precharge inside the current envelope of a 4-bank part',
          'On every device, always',
          'Never - they are the same parameter',
          'Only below 85 C'
        ],
        chapter: 'timing', hard: false,
        explanation: '4-bank parts: tRPab = tRPpb. 8-bank parts precharging all banks at once draw more current, so tRPab grows (18/21/27 ns vs 15/18/24).',
        source: 'JESD209-2F sec 5.9' },

      { q: 'What is the LPDDR2 write-to-read command spacing (S4)?',
        answers: [
          'WL + 1 + BL/2 + RU(tWTR/tCK) clocks',
          'BL/2 + 2 clocks',
          'RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL clocks',
          'tCCD = 2 clocks'
        ],
        chapter: 'timing', hard: true,
        explanation: 'WR -> RD = WL + 1 + BL/2 + RU(tWTR/tCK). (The RL + tDQSCK + BL/2 + 1 - WL formula is the READ-to-write direction - this book\'s tRTW. BL is the effective burst length if the write was BST-truncated.)',
        source: 'JESD209-2F sec 5.9.1' },

      { q: 'Why does the LPDDR2 read-to-write formula include RU(tDQSCKmax/tCK)?',
        answers: [
          'With no DLL, the read strobe/data can arrive several clocks after the RD; the bus must stay read-owned until the latest possible data clears before write data drives',
          'It accounts for the ODT settling time',
          'It is the write preamble length',
          'It converts between CK and DQS domains on S2 only'
        ],
        chapter: 'timing', hard: true,
        explanation: 'tRTW = RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL (book symbol): wait out read latency plus the worst-case multi-clock strobe access, finish the burst plus one bubble, then credit back WL because write data is timed from the WR command.',
        source: 'JESD209-2F sec 5.9.2' },

      { q: 'After a Burst Terminate (BST), what is the effective burst length used in every spacing formula?',
        answers: [
          '2 x (clocks from the RD/WR command to the BST)',
          'Always BL4',
          'BL/2 regardless of when BST lands',
          'Zero - BST cancels the transfer entirely'
        ],
        chapter: 'commands', hard: true,
        explanation: 'BST truncates the most recent RD or WR; effective BL = 2 x (clocks from RD/WR to BST). The truncation itself lands one full RL (reads) or WL (writes) later, and RD<->WR interruption is never allowed - BST is the only way to cut across directions.',
        source: 'JESD209-2F sec 5.3' },

      { q: 'What is the LPDDR2 refresh contract?',
        answers: [
          'R refreshes must land in EVERY rolling tREFW window (32 ms at <=85 C) - any pattern, regular or bursted, is legal',
          'One REF exactly every tREFI, hard deadline',
          'Refresh is fully automatic; the controller does nothing',
          '8 REFab per tRFC window, whatever the temperature'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'tREFI is only a reference average. The binding rules: R REFab-equivalents per rolling tREFW, and at most 8 REFab per rolling tREFBW. Bursting a whole window\'s refreshes then idling ~30 ms is legal.',
        source: 'JESD209-2F sec 5.10' },

      { q: 'Who chooses the target bank of a per-bank refresh (REFpb)?',
        answers: [
          'The device\'s own round-robin counter - synchronized to bank 0 at reset, at every self-refresh exit and at every REFab; the controller must shadow it',
          'The controller, via the CA bus bank field',
          'Always bank 0',
          'The temperature sensor'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'REFpb carries no bank address: the device picks the target round-robin. Since the counter re-syncs at reset, SRX and REFab, the controller must shadow those events to know which bank is next. 8 REFpb replace one REFab.',
        source: 'JESD209-2F sec 5.11' },

      { q: 'How does partial-array self-refresh (PASR) work on S4 parts?',
        answers: [
          'MR16 is a per-bank mask and MR17 adds a per-segment mask (1 Gb+); a location is refreshed only if BOTH its bank and its segment are unmasked - masked regions lose their data',
          'MR16 picks full/half/quarter array anchored at the LAST bank',
          'PASR only exists on S2',
          'It refreshes masked regions at half rate instead'
        ],
        chapter: 'refresh', hard: true,
        explanation: 'S4: MR16 masks banks individually; MR17 masks 8 row-space segments; the masks combine (bank AND segment unmasked to survive). S2 instead picks full/1/2/.../1/8 anchored at bank 0. Masked regions are simply not refreshed.',
        source: 'JESD209-2F sec 5.12' },

      { q: 'What does the MR4 temperature readout let the controller do?',
        answers: [
          'Scale refresh rate to the device\'s own recommendation (4x/2x/1x/0.25x tREFI) - the 0.25x option below 85 C roughly quarters refresh power - and apply the 1.875 ns AC de-rate when flagged',
          'Read the exact die temperature in degrees',
          'Skip refresh entirely below 85 C',
          'Re-train the DQS capture automatically'
        ],
        chapter: 'refresh', hard: false,
        explanation: 'TCSR: the device posts a recommended refresh rate in MR4 (sensor updates at most every tTSI = 32 ms). The controller polls it - fast enough to track a 2 C gradient budget - and adjusts; the de-rate flag adds 1.875 ns to core timings at the hot end.',
        source: 'JESD209-2F sec 5.12.1' }
    ],

    commandDocs: [
      { cmd: 'ACT', name: 'Activate',
        description: 'Opens row R in bank B - on LPDDR2 the ROW address ' +
                     'comes out here, two edges of the 10-bit CA bus at ' +
                     'once. Spacing: tRCD to the first column command, ' +
                     'tRRD to the next ACT, tFAW across any four, tRC same ' +
                     'bank.' },
      { cmd: 'RD', name: 'Read',
        description: 'Bursts BL words from the open row; the COLUMN ' +
                     'address goes out with this command (C1-C10), and CA0 ' +
                     'on the falling edge is the auto-precharge flag. Data ' +
                     'returns RL clocks later with an uncalibrated ' +
                     'tDQSCK wander.' },
      { cmd: 'WR', name: 'Write',
        description: 'Bursts BL words into the open row; column address ' +
                     'and AP flag same as RD. First data lands WL clocks ' +
                     'after the command; DQS is differential and ' +
                     'unidirectional here.' },
      { cmd: 'RDA', name: 'Read with Auto-Precharge',
        description: 'RD with CA0(f) = 1: the bank precharges itself once ' +
                     'tRAS and tRTP are met. Re-activation waits tRP past ' +
                     'the internal precharge and tRC from the old ACT.' },
      { cmd: 'WRA', name: 'Write with Auto-Precharge',
        description: 'WR with CA0(f) = 1: the bank precharges itself ' +
                     'after write recovery (WL + BL/2 + tWR past the ' +
                     'command). Re-activation waits tRP and tRC.' },
      { cmd: 'PRE', name: 'Precharge',
        description: 'Closes an open row. One flag chooses the target: ' +
                     'AB = 0 precharges the one bank on BA0-BA2 (tRPpb), ' +
                     'AB = 1 precharges all banks (tRPab, longer). Starts ' +
                     'tRAS after the ACT that opened the row.' },
      { cmd: 'BST', name: 'Burst Terminate',
        description: 'Stops a read or write burst in flight; the burst ' +
                     'ends a fixed latency after BST (RL for reads, WL for ' +
                     'writes). Only legal burst lengths survive - the ' +
                     'device truncates on the internal boundary.' },
      { cmd: 'MRW', name: 'Mode Register Write',
        description: 'Writes any of the 64 mode registers: MR selects the ' +
                     'register, OP carries the value. All banks idle; tMRW ' +
                     'spacing to the next command. Carries BL, RL/WL, ' +
                     'refresh and PASR options.' },
      { cmd: 'MRR', name: 'Mode Register Read',
        description: 'Reads a mode register back onto DQ0-DQ7 after RL ' +
                     'clocks - how the host learns device id, revision and ' +
                     'status (e.g. refresh-needed flags). Like a 1-word ' +
                     'read that needs no open row.' },
      { cmd: 'REFab', name: 'Refresh All Banks',
        description: 'One all-bank refresh step; all banks idle first, ' +
                     'device busy for tRFCab. Average rate tREFI, up to 8 ' +
                     'postponable. Resynchronizes the per-bank refresh ' +
                     'counter the controller must shadow.' },
      { cmd: 'REFpb', name: 'Refresh Per Bank',
        description: 'Refreshes ONE bank (BA0-BA2) for tRFCpb, so the ' +
                     'other seven stay schedulable - the LPDDR2 latency ' +
                     'hiding trick. Banks are refreshed round-robin by an ' +
                     'internal counter that resets at reset, SRX and ' +
                     'every REFab.' },
      { cmd: 'SRE/DPD', name: 'Self-Refresh / Deep Power-Down',
        description: 'Entered from the same encoding when CKE falls with ' +
                     'all banks idle: MR0 OP picks self-refresh (device ' +
                     'refreshes itself, tCKESR min) or DPD (no refresh - ' +
                     'data is lost). Exit: tXSR to commands, longer to ' +
                     'reads.' },
      { cmd: 'NOP/DES', name: 'No Operation / Deselect',
        description: 'Filler cycles keeping the CA bus valid while timing ' +
                     'windows drain - one command occupies one clock on ' +
                     'LPDDR2 (two edges), so NOPs are cheap.' }
    ],

    scenarioTweaks: {
      excludeGenerators: [],
      extraTags: [],
      defaultPolicy: 'open',
      turnaround: { wtr: '(tWTR bubble)', rtw: '(tRTW bubble)' }
    }
  });
})(DDRD);
