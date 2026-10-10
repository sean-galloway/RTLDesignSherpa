# Walkthrough: AXI Write to an Idle Bank

## Scenario

An AXI4 write (AW + 4 W beats, 16 bytes) maps to bank B1, row R2,
column C0. B1 is idle (no open row).

## Command trace

```
ACT B1 R2        ; open the row (bank was idle - no PRE needed)
--- (tRCD) ---   ; row-to-column delay
WR  B1 C0        ; burst write, AP=0; write data starts WL*tCK + tDQSS later
NOP              ; burst occupies the DQ bus; tWR recovery runs from
                 ; the last data, then the bank may be precharged
```

## Why each command

- `ACT B1 R2` - an idle bank needs no precharge; ACT is legal as long
  as tRRD from the previous ACT (any bank) and the tFAW window (max 4
  ACTs per rolling tFAW, 8-bank parts) are met.
- `--- (tRCD) ---` - same row-to-column delay as a read.
- `WR B1 C0` - CA2r=L marks a write. The controller drives DQS with a
  tWPRE preamble and the first data WL clocks (plus tDQSS) after the
  command. Each beat must meet tDS/tDH around the DQS edge; DM pins
  mask any beats that should not be written.
- The trailing NOPs cover tWR (write recovery, typ 15 ns from the end
  of the burst data): the bank may not be precharged until tWR has
  elapsed, because the write is still being committed to the array.

## AXI view

- AW and W channels carry the request; the DRAM does not see them
  separately - the controller issues WR only when it has (or is about
  to have) the write data, since LPDDR2 gives it no way to stall
  mid-burst.
- B (write response) can be returned once the data is accepted by the
  DRAM schedule; the tWR window is a DRAM-internal matter.

## What to notice

- An idle-bank write miss costs tRCD, half the read-miss penalty - no
  tRP because nothing was open.
- Alternative: issue `WR B1 C0` with AP=1. The device then
  auto-precharges after nWR clocks, and the bank returns to idle with
  no explicit PRE - at the price of having programmed nWR = RU(tWR/tCK)
  correctly in MR1.
- tWR is the write-side analog of tRTP on the read side: both gate the
  PRE; both exist because the burst's last data and the array's
  precharge cannot overlap.

**Source:** JESD209-2F sections 5.1, 5.5, 5.9.2-5.9.3 (derived walkthrough)
