# Walkthrough: AXI Read, Row Already Open

Configuration used in all Chapter 4 traces (the drill model): BL = 8, RL = 6,
WL = 3, flat 8-bank device. Banks B0-B7, rows R0-R7, columns C0-C7.

## Scenario

An AXI4 master issues a read that maps to bank B3, row R5, column C2. Row R5
is already open in B3, so the access is a row hit.

## Command trace

```
RD  B3 C2        ; row already open - issue the burst immediately
NOP              ; tCCD = 4 clocks minimum between column commands
NOP              ; read data returns after RL*tCK + tDQSCK
NOP              ; DQS may arrive over a wide window because there is no DLL
```

## Why each command

- `RD B3 C2` - the row is open, so no ACT is needed. CA2r=H selects a read;
  C2 is the burst start column; AP=0 (CA0f) so the row stays open.
- LPDDR3 uses a fixed burst length of 8. There is no burst-chop option; every
  RD delivers eight contiguous words from the array.
- The first DQS edge appears RL clocks after the command, plus the tDQSCK
  window. Because LPDDR3 has no DLL, tDQSCK is a loose min-to-max range that
  can span more than one clock. The controller must sample data relative to
  the strobe, not to a fixed CK edge.
- No PRE: leaving the row open is the open-page policy; a later access to R5
  in B3 is again a hit.

## AXI view

- AR channel: one burst request. With a 32-bit DQ bus, BL8 covers 32 bytes in
  one DRAM burst.
- A wider AXI transaction would be split into multiple RD commands spaced
  tCCD apart, e.g. `RD B3 C2`, then `RD B3 C4` four clocks later.

## What to notice

- A row hit costs exactly one CA cycle on the command bus. Everything else
  (tCCD, turnaround) is about scheduling the next access around it.
- The controller tracks one open row per bank; that bookkeeping determines
  whether an AXI request becomes a hit or a miss.

**Source:** JESD209-3C sections 3, 4.2, 4.4, 4.17.1 (derived walkthrough)
