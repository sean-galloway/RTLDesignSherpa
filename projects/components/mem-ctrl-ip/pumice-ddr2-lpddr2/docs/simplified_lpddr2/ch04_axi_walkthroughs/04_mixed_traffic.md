# Walkthrough: Mixed Reads and Writes

## Scenario

Three AXI requests arrive close together:

1. Read: bank B3, row R5 (open), column C2.
2. Write: bank B1, row R2 (open), column C0.
3. Read: bank B1, row R2, column C4.

Both rows are already open, so this trace is pure bus scheduling: the
DQ bus is shared, and read/write direction changes cost bubbles.

## Command trace

```
RD  B3 C2        ; read burst 1: data out after RL + tDQSCK
--- (turnaround) ---  ; read-to-write bubble, see below
WR  B1 C0        ; write burst: DQ direction flips
--- (tWTR) ---   ; write-to-read recovery before any new RD
RD  B1 C4        ; read burst 2, same open row as the write - a hit
PRE B1           ; done with B1 (tRTP after the RD met); close it
```

## Why each gap

- Read-to-write turnaround: the write command may be issued no earlier
  than RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL clocks after the read
  command. With RL=3, WL=1, BL=4 and tDQSCKmax fitting in 2 clocks that
  is 3 + 2 + 2 + 1 - 1 = 7 clocks. The bubble exists because read data
  is still leaving the DRAM (tDQSCK is long and unpipelined - there is
  no DLL) and the DQ bus must be idle before the controller starts
  driving write data.
- Write-to-read: the next read command waits
  WL + 1 + BL/2 + RU(tWTR/tCK) after the write command
  (1 + 1 + 2 + RU(7.5 ns/tCK) here). tWTR lets the write data finish
  propagating into the array before sense amps are asked to read.
- `RD B1 C4` - same bank, same row as the write: a row hit even though
  a write happened in between. Open-row state is per bank, not per
  access type.
- `PRE B1` - legal once tRAS (from the ACT that opened R2) and tRTP
  (from RD B1 C4) are both met.

## AXI view

AXI is oblivious to direction changes; its read and write channels are
independent. The DRAM bus is not: every RD->WR or WR->RD transition on
the shared DQ pins costs turnaround clocks, so a controller that groups
reads with reads and writes with writes (batching) measurably outruns
one that serves requests strictly in arrival order.

## What to notice

- Turnarounds, not tRCD, dominate lightly-loaded mixed traffic.
- LPDDR2 has no ODT to switch and no tRTW parameter - the turnaround
  rules are formulas over RL, WL, BL and tDQSCK, all given in
  Chapter 6.
- tCCD still applies between the two column commands: even without the
  direction change, bursts on the shared bus must not collide.

**Source:** JESD209-2F sections 5.4, 5.5, 5.9.1 (derived walkthrough)
