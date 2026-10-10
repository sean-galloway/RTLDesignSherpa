# Walkthrough: Mixed Reads and Writes

## Scenario

Three AXI requests arrive close together:

1. Read: bank B3, row R5 (open), column C2.
2. Write: bank B1, row R2 (open), column C0.
3. Read: bank B1, row R2, column C4.

Both rows are already open, so this trace is pure bus scheduling: the DQ bus
is shared, and read/write direction changes cost bubbles.

## Command trace

```
RD  B3 C2        ; read burst 1: data out after RL + tDQSCK
--- (tRTW) ---   ; read-to-write turnaround, see below
WR  B1 C0        ; write burst: DQ direction flips
--- (tWTR) ---   ; write-to-read recovery before any new RD
RD  B1 C4        ; read burst 2, same open row as the write - a hit
PREpb B1         ; done with B1 (tRTP after the RD met); close it
```

## Why each gap

- Read-to-write turnaround (book symbol tRTW): the write command may be
  issued no earlier than RL + RU(tDQSCK(MAX)/tCK) + BL/2 + 1 - WL clocks
  after the read command. With RL=6, WL=3, BL=8 and tDQSCK(MAX)=2 clocks,
  that is 6 + 2 + 4 + 1 - 3 = 10 clocks. The bubble exists because read data
  is still leaving the DRAM and the DQ bus must be idle before the controller
  starts driving write data. LPDDR3 has no DLL, so tDQSCK is a wide window
  rather than a locked edge; the controller must budget the worst-case
  tDQSCK(MAX).
- Write-to-read: the next read command waits
  WL + 1 + BL/2 + RU(tWTR/tCK) clocks after the write command
  (3 + 1 + 4 + 4 = 12 clocks here). tWTR lets the write data finish
  propagating into the array before sense amps are asked to read.
- `RD B1 C4` - same bank, same row as the write: a row hit even though a
  write happened in between. Open-row state is per bank, not per access type.
- `PREpb B1` - legal once tRAS (from the ACT that opened R2) and tRTP (from
  RD B1 C4) are both met. A PREab would have cost tRPab and closed every
  bank.

## AXI view

AXI is oblivious to direction changes; its read and write channels are
independent. The DRAM bus is not: every RD->WR or WR->RD transition on the
shared DQ pins costs turnaround clocks, so a controller that groups reads
with reads and writes with writes (batching) measurably outruns one that
serves requests strictly in arrival order.

## What to notice

- Turnarounds, not tRCD, dominate lightly-loaded mixed traffic.
- tCCD still applies between column commands: even without the direction
  change, bursts on the shared bus must not collide. With BL=8, tCCD is 4
  clocks.
- tFAW limits activate parallelism: no more than four ACT or REFpb commands
  may fall inside a rolling tFAW window on this 8-bank device.
- Refresh appears as REFab in most schedules, but REFpb exists as a
  per-bank alternative that refreshes one bank while others remain active.

**Source:** JESD209-3C sections 4.4, 4.5, 4.7, 4.8, 4.17.1 (derived walkthrough)
