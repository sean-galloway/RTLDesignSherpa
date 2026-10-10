# Walkthrough: AXI Read, Row Already Open

Configuration used in all Chapter 4 traces (the drill model): RL = 10, WL = 6,
BL = 16, flat 8-bank device, single channel view (channel A). Banks B0-B7,
rows R0-R7, columns C0-C7. LPDDR4 is dual-channel per die; channel B runs on
its own independent command/data bus and is not shown here.

## Scenario

An AXI4 master issues a read that maps to bank B3, row R5, column C2. Row R5
is already open in B3, so the access is a row hit.

## Command trace

```
RD  B3 C2        ; row already open - issue the burst immediately
NOP              ; tCCD = 8 clocks minimum between BL16 column commands
NOP              ; read data returns after RL clocks plus tDQSCK
NOP              ; DQS may arrive over a window because there is no DLL
NOP
NOP
NOP
NOP
NOP
```

The BL16 burst delivers 16 data words (D0-D15) across 8 clock cycles on the
DQ bus. Because the drill model only has columns C0-C7, the burst wraps the
8-column address space twice.

## Why each command

- `RD B3 C2` - the row is open, so no ACT is needed. The read is a two-cycle
  CA command; CA2r=H selects a read, C2 is the burst start column, and AP=0
  leaves the row open.
- LPDDR4 supports BL16 and BL32; this trace uses BL16. A BL16 read transfers
  16 contiguous words from the array. tCCD is 8 clocks for BL16.
- The first DQS edge appears RL clocks after the command, offset by tDQSCK.
  LPDDR4 has no DLL, so tDQSCK is a min-to-max window rather than a locked
  edge. The controller samples data relative to the strobe.
- No PRE: leaving the row open is the open-page policy; a later access to R5
  in B3 is again a hit.

## AXI view

- AR channel: one burst request. With a 16-bit DQ bus, BL16 covers 32 bytes
  in one DRAM burst.
- A wider AXI transaction would be split into multiple RD commands spaced
  tCCD apart, e.g. `RD B3 C2`, then `RD B3 C4` eight clocks later.

## What to notice

- A row hit costs exactly two CA cycles on the command bus. Everything else
  (tCCD, turnaround) is about scheduling the next access around it.
- The controller tracks one open row per bank; that bookkeeping determines
  whether an AXI request becomes a hit or a miss.

**Source:** JESD209-4E sections 2.1, 4.1, 4.6, 4.7 (derived walkthrough)
