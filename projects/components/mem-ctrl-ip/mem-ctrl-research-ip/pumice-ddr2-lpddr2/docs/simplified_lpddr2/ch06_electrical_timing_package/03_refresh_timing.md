# Refresh Timing

LPDDR2 gives the controller unusual freedom in WHEN refreshes happen:
a count of refresh commands owed per rolling window, two granularities
(all-bank and per-bank), and a temperature-scaled rate. This file is
the complete picture.

## The contract

| Symbol | Definition | Value |
| --- | --- | --- |
| tREFW | Rolling refresh window: R refreshes must land in every window | 32 ms (Tcase <= 85 C); 8 ms (85-105 C) |
| R | Required REFab count per tREFW | 2048 (64-128 Mb), 4096 (256 Mb-1 Gb), 8192 (2-8 Gb) |
| tREFI | Average all-bank refresh interval (= tREFW / R, reference only) | 15.6 / 7.8 / 3.9 us by density |
| tREFIpb | Average per-bank refresh interval (reference only) | 0.975 us (1 Gb S4), 0.4875 us (2-8 Gb) |
| tRFCab | All-bank refresh cycle time: device busy | 90 ns (<=1 Gb), 130 ns (2-4 Gb), 210 ns (6-8 Gb) |
| tRFCpb | Per-bank refresh cycle time: target bank busy | 60 ns (<=4 Gb), 90 ns (6-8 Gb) |
| tREFBW | Burst refresh window: at most 8 REFab in any rolling window of this length | 4 x 8 x tRFCab (2.88 / 4.16 / 6.72 us) |

One REFab may be replaced by a full round of eight REFpb (which is why
tREFIpb = tREFI / 8). REFpb exists only on 8-bank devices (1 Gb S4 and
up); S2 devices are REFab-only below 4 Gb.

## Scheduling freedom, and its limits

- Regular pattern: one REFab every tREFI (or one REFpb every tREFIpb).
  Self-refresh may be entered at any time.
- Burst/pause pattern: up to 8 REFab per rolling tREFBW, then silence
  until the window count demands more. In the extreme, an entire
  window's R refreshes can be bursted, leaving up to
  tREFW - R x 4 x tRFCab refresh-free (about 30 ms for a 1 Gb S4).
- Any pattern is legal if EVERY rolling tREFW contains R refreshes and
  every rolling tREFBW contains at most 8 REFab. Transitions between
  patterns are where violations happen: entering self-refresh is only
  safe directly after a burst phase, because self-refresh behaves like
  the regular distributed pattern inside the window math.

## Self-refresh interaction

Time in self-refresh earns credit: the required count in a window
containing tSRF of self-refresh drops to R* = R - RU(tSRF / tREFI).
After exit (tXSR = tRFCab + 10 ns), at least one refresh (1 REFab or a
full round of 8 REFpb) must be issued before the next self-refresh
entry, because an internal refresh may have been cut short at exit.

## REFpb mechanics

- The target bank is chosen by the device's round-robin counter,
  synchronized to bank 0 at reset, at every self-refresh exit, and at
  every REFab. The controller must shadow this counter.
- During tRFCpb only the target bank is busy; all other banks may be
  activated, read or written. REFpb also counts as a bank activation
  for tFAW.
- Separations: tRFCpb after a REFpb before ACT-to-same-bank or the
  next REF; tRFCab after REFab before anything; only tRRD before an
  ACT to a different bank than the REFpb target; tRP after a PRE before
  refreshing that bank.

## PASR - partial array self-refresh

In self-refresh, masked regions are simply not refreshed (and lose
their data), cutting standby current:

- S2: MR16 picks full / 1/2 / 1/4 / 1/8 array, anchored at bank 0.
- S4: MR16 is a per-bank mask; MR17 (1 Gb and up) adds a per-segment
  mask over 8 row-space segments. Bank and segment masks combine: a
  location is refreshed only if its bank and segment are both unmasked.

## Temperature-compensated self refresh (TCSR)

The device reads its own temperature and posts a recommended refresh
rate in MR4 (4x / 2x / 1x / 0.25x tREFI, with a de-rate flag at the
high end). The controller polls MR4 - the internal sensor updates at
most every tTSI = 32 ms, and the read interval must satisfy
TempGradient x (ReadInterval + tTSI + SysRespDelay) <= 2 C - and scales
its refresh rate (and, above 85 C, de-rates core AC timings by
1.875 ns). Below 85 C the 0.25x option roughly quarters refresh power.

**Source:** JESD209-2F sections 5.10-5.12.1, 12.3 (Tables 101-102),
12.4 (Table 103)
