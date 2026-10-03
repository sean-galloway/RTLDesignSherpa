# Walkthrough: Mixed Reads and Writes

Configuration used in all Chapter 4 traces (the drill model): RL = 10, WL = 6,
BL = 16, flat 8-bank device, single channel view (channel A).

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
NOP              ; read-to-write turnaround (book symbol tRTW)
NOP              ; formula: RL + RU(tDQSCKmax/tCK) + BL/2 - WL + tWPRE + RD(tRPST)
NOP              ; with drill values (2tCK preamble, 0.5nCK postamble, tDQSCKmax=2tCK): 16 clocks
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
WR  B1 C0        ; write burst: DQ direction flips, data starts WL+tDQSS later
NOP              ; write-to-read recovery (book symbol tWTR)
NOP              ; formula: WL + 1 + BL/2 + RU(tWTR/tCK)
NOP              ; with drill values: 6 + 1 + 8 + 6 = 21 clocks
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
NOP
RD  B1 C4        ; read burst 2, same open row as the write - a hit
NOP
NOP
NOP
NOP
NOP
NOP
NOP
PREpb B1         ; done with B1 (tRTP after the RD met); close it
```

## Why each gap

- Read-to-write turnaround (book symbol tRTW): the write command may be
  issued no earlier than RL + RU(tDQSCK(MAX)/tCK) + BL/2 - WL + tWPRE +
  RD(tRPST) clocks after the read command. With RL=10, WL=6, BL=16, a 2tCK
  write preamble, 0.5nCK postamble, and a representative tDQSCK(MAX) of 2tCK,
  the gap is 16 clocks. The bubble exists because read data is still leaving
  the DRAM and the DQ bus must be idle before the controller starts driving
  write data. LPDDR4 has no DLL, so the controller must budget the worst-case
  tDQSCK(MAX).
- Write-to-read: the next read command waits
  WL + 1 + BL/2 + RU(tWTR/tCK) clocks after the write command
  (6 + 1 + 8 + 6 = 21 clocks here). tWTR lets the write data finish
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
  change, bursts on the shared bus must not collide. With BL=16, tCCD is 8
  clocks.
- tFAW limits activate parallelism: no more than four ACT or REFpb commands
  may fall inside a rolling tFAW window on this 8-bank device.
- Refresh appears as REFab in most schedules, but REFpb exists as a
  per-bank alternative that refreshes one bank while others remain active.
  LPDDR4 also adds Refresh Management (RFM): when the device advertises RFM
  support, the controller must issue RFM commands after a programmed number
  of ACTs to keep row-activation charge at safe levels.
- LPDDR4 is dual-channel per die. This trace follows channel A only;
  channel B runs independently on its own CA/DQ/DQS pins and can schedule
  its own reads and writes in parallel.
- Masked writes are available (Masked Write command + DMI pins), but this
  trace uses a plain WR for clarity.

**Source:** JESD209-4E sections 4.1, 4.2, 4.6, 4.10, 4.13.2, 4.17, 4.19, 4.47
(derived walkthrough)
