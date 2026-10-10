# Refresh and Self-Refresh Timing

## Refresh parameters: fine granularity

DDR4 keeps refresh all-bank (there is no per-bank refresh command) and
adds fine granularity refresh (FGR): the controller picks the refresh
mode in MR4 and gets a matching tREFI/tRFC pair.

| Mode | Interval (avg) | tRFC min by density |
| --- | --- | --- |
| 1x (default) | tREFI1 = 7.8 us (3.9 us above 85 C) | 160 / 260 / 350 / 450 (or 350 opt) ns at 2 / 4 / 8 / 16 Gb |
| 2x | tREFI2 = tREFI1 / 2 | 110 / 160 / 260 / 350 (or 260 opt) ns |
| 4x | tREFI4 = tREFI1 / 4 | 90 / 110 / 160 / 260 (or 160 opt) ns |

Rules:

- Fixed 1x, 2x, or 4x mode allows only the matching REF1x/REF2x/REF4x
  command; on-the-fly variants of 1x/2x and 1x/4x allow mixing.
- Higher granularity buys shorter busy windows at the cost of more
  commands: at 8 Gb, 1x stalls 350 ns every 7.8 us (~4.5% duty), while
  4x stalls 160 ns every 1.95 us - friendlier to tight schedules, and
  mandatory thinking when the memory is hot (tREFI halves above 85 C
  in every mode).
- All banks must be precharged (tRP met) before any REF; the tREFI
  average bounds the long-term rate, and posting/pull-in slack follows
  the same 9 x tREFI-style windows as earlier generations.

## Self-refresh

| Symbol | Definition | Value |
| --- | --- | --- |
| tCKE | Minimum CKE pulse, high or low | max(3 nCK, 5 ns) |
| tCKESR | Minimum CKE low for self-refresh entry to exit | tCKE(min) + 1 nCK |
| tXS | Exit self-refresh to non-DLL commands | max(tRFC + 10 ns window per bin) |
| tXSDLL | Exit self-refresh to DLL-requiring commands | tDLLK (see below) |
| tDLLK | DLL re-lock time | 597 / 768 / 1024 nCK by speed, programmed via MR6 |

DDR4 adds a self-refresh abort option (MR4 A9): instead of the full tXS
wait, a fast-exit path returns to normal operation sooner at the risk of
abandoning an in-flight internal refresh - the controller must then
issue an explicit REF to make up the gap. Exit is otherwise the familiar
pattern: stable clock, CKE high, NOP/DES through the window, then tXS
(non-DLL) or tXSDLL (reads, DLL re-locking).

## Power-down timings

| Symbol | Definition | Value |
| --- | --- | --- |
| tXP | Exit power-down (DLL running) to any valid command | max(4 nCK, 6 ns) |
| tCPDED | Command pass disable after PD entry | 4 nCK |
| tPD | PD entry to exit window | tCKE(min) to 9 x tREFI |

Precharge power-down freezes the DLL; commands needing the DLL (reads)
wait out the longer DLL-relock exit, and the ODT turns asynchronous
while the DLL is frozen (the tAONPD/tAOFPD windows). Active power-down
keeps the DLL running for a tXP-class resume. Power-down performs no
refresh: the stay is bounded by the refresh schedule, 9 x tREFI at
best with REFs posted ahead.

ZQ calibration runs as ZQCL (long, init/after-power events) and ZQCS
(short, periodic) - DDR4 drops the DDR3-era ZQreset form.

**Source:** JESD79-4D sections 4.9, 4.17, 4.26, 11.1 (Table 154), 13 (AC tables)
