# Walkthrough: AXI Write to an Idle Bank

Configuration used in all Chapter 4 traces (the drill model): RL = 10, WL = 6,
BL = 16, flat 8-bank device, single channel view (channel A).

## Scenario

An AXI4 write request maps to bank B1, row R2, column C0. B1 is idle (no open
row).

## Command trace

```
ACT B1 R2        ; open the row (bank was idle - no PRE needed)
--- (tRCD) ---   ; row-to-column delay
WR  B1 C0        ; burst write, AP=0; write data starts WL*tCK + tDQSS later
NOP              ; burst occupies the DQ bus; tWR recovery runs from
NOP              ; the last data, then the bank may be precharged
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
```

The BL16 burst drives 16 data words (D0-D15) across 8 clocks, wrapping the
C0-C7 drill model twice. LPDDR4 also supports masked writes via the Masked
Write command and DMI pins; this trace uses a plain WR for simplicity.

## Why each command

- `ACT B1 R2` - an idle bank needs no precharge; ACT is legal as long as
  tRRD from the previous ACT (any bank) and the tFAW window (max 4 ACTs in a
  rolling tFAW on 8-bank parts) are met.
- `--- (tRCD) ---` - same row-to-column delay as a read.
- `WR B1 C0` - the write is a two-cycle CA command. The controller drives DQS
  with a 2tCK preamble and the first data WL clocks (plus tDQSS) after the
  command. Each beat must meet tDS/tDH around the DQS edge. WDQS_on/off
  timing governs when DQS must be differential around the write; it can be
  ignored when it overlaps read bursts or turnarounds.
- The trailing NOPs cover tWR (write recovery from the end of the burst
  data): the bank may not be precharged until tWR has elapsed, because the
  write is still being committed to the array. The minimum WR-to-PRE spacing
  for the same bank is WL + 1 + BL/2 + RU(tWR/tCK) clocks.

## AXI view

- AW and W channels carry the request; the DRAM does not see them separately.
  The controller issues WR only when it has (or is about to have) the write
  data, because LPDDR4 gives it no way to stall mid-burst.
- B (write response) can be returned once the data is accepted by the DRAM
  schedule; the tWR window is a DRAM-internal matter.

## What to notice

- An idle-bank write miss costs tRCD, half the read-miss penalty - no tRP
  because nothing was open.
- Alternative: issue `WR B1 C0` with AP=1. The device then auto-precharges
  after the burst, and the bank returns to idle with no explicit PREpb - at
  the price of having programmed nWR correctly in MR1.
- tWR is the write-side analog of tRTP on the read side: both gate the PRE;
  both exist because the burst's last data and the array's precharge cannot
  overlap.

**Source:** JESD209-4E sections 4.1, 4.10, 4.13.2, 4.17.2 (derived walkthrough)
