# Walkthrough: AXI Read, Row Already Open

Configuration used in all Chapter 4 traces (the drill model): S4
device, BL = 4, RL = 3, WL = 1, sequential/wrap bursts. Banks B0-B7,
rows R0-R7, columns C0-C7.

## Scenario

An AXI4 master issues a 32-bit read (ARLEN = 3 on a 32-bit bus, i.e. 4
beats = 16 bytes) at an address that maps to bank B3, row R5, column C2.
Row R5 is already open in B3 from an earlier access.

## Command trace

```
RD  B3 C2        ; row already open - issue the burst immediately
NOP              ; tCCD = 2 clocks minimum between bursts (bus stays quiet)
NOP              ; read data returns RL*tCK + tDQSCK + tDQSQ after RD
```

## Why each command

- `RD B3 C2` - the row is open, so no ACT is needed. CA2r=H marks a
  read; C2 is the burst start column; AP=0 (CA0f) so the row stays open
  for the next access.
- The burst delivers 4 words (BL=4) on each DQ edge-aligned to DQS,
  starting RL clocks (plus tDQSCK) after the command.
- No PRE: leaving the row open is the open-page policy; a later access
  to R5 in B3 is again a hit.

## AXI view

- AR channel: one 16-byte burst request.
- The DRAM burst of 4 words x (bus width) covers it exactly at BL=4 on a
  32-bit DQ interface. A wider AXI beat count or narrower DRAM bus would
  need multiple RD commands spaced tCCD apart, e.g. `RD B3 C2`,
  `RD B3 C4` two clocks later, data returning back-to-back.

## What to notice

- A row hit costs exactly one CA cycle on the command bus. Every other
  scheduling rule (tCCD, turnaround) is about packing the next command
  around it.
- The controller knew this was a hit because it tracks one open row per
  bank - that bookkeeping is the whole game.

**Source:** JESD209-2F sections 5.3, 5.4 (derived walkthrough)
