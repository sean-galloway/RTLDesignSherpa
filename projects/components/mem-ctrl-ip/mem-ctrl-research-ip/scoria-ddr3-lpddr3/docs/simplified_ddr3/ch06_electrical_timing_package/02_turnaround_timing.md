# Turnaround and Burst Timing

Column-command spacing and bus-direction rules. These are the parameters
that decide how full the DQ bus can be kept.

## CAS-to-CAS and latencies

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tCCD | Column command to column command, same or different banks | RD/WR -> RD/WR (any direction, same type) | 4 clocks |
| RL | Read latency: command to first data | RD -> first DQS/DQ out | AL + CL clocks |
| WL | Write latency: command to first strobe | WR -> first DQS in | AL + CWL clocks |
| CL | CAS latency component of RL | internal CAS -> data | 5-11 clocks (MR0; CL 5/6 share an encoding bit pattern with A2) |
| CWL | CAS write latency component of WL | internal write -> first DIN | 5-8 clocks (MR2) |
| AL | Additive latency: posted-CAS hold | RD/WR command -> internal CAS | 0, CL-1, or CL-2 (MR1) |

BL/2 clocks of bus occupancy per burst: BC4 occupies 2 clocks of DQ, BL8
occupies 4. Seamless same-direction traffic means issuing a column command
every BL/2 clocks - at BL8 that is exactly tCCD = 4, so back-to-back BL8
bursts just saturate the bus.

Note the DDR3 change from DDR2: WL is programmed independently via CWL,
not derived as RL - 1. A controller may run CL = 9 with CWL = 7; the
write tail no longer slavishly follows the read latency.

## Direction changes

Note on tRTW: JESD79-3F never names the read-to-write parameter (the
symbol does not appear in the spec). It does specify the spacing: RL +
tCCD + 2 - WL for BL8, and RL + tCCD/2 + 2 - WL when the read is chopped
to BC4. This book calls the parameter tRTW, matching the other books in
this series, which keeps the timing tables comparable across
technologies.

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tRTW | Read-to-write turnaround: read burst and postamble must clear before the write preamble (book symbol; the spec gives the relation unnamed) | RD(any bank) -> WR(any bank) | RL + tCCD + 2 - WL at BL8: 6 clocks when RL = WL |
| tWTR | Write-to-read: last write data must leave the input path before a read reuses the array | first CK after last write data(any) -> internal RD(any) | max(4 nCK, 7.5 ns) |

Command-spacing forms:

| Transition | Spacing from first command (clocks) |
| --- | --- |
| RD -> WR | RL + tCCD + 2 - WL (= BL/2 + 2 when RL = WL) |
| WR -> RD | WL + BL/2 + RU(tWTR) |
| RD -> RD | max(tCCD, BL/2) |
| WR -> WR | max(tCCD, BL/2) |

Worked example (the Chapter 4 configuration: CL = 5, CWL = 5, AL = 0, so
RL = WL = 5; BL8; tWTR = 5 clk): RD->WR = 4 + 2 = 6 clocks, WR->RD =
5 + 4 + 5 = 14 clocks. The asymmetry is the write path's long internal
tail (WL plus the tWTR analog window); reads turn into writes far cheaper
than writes turn into reads - the opposite ranking from the latency
numbers alone would suggest.

## Strobe-level timing (for completeness)

These bound the DQS/DQ relationship rather than the scheduler, but the
controller's PHY must meet them:

| Symbol | Definition | Value |
| --- | --- | --- |
| tDQSS | Write DQS rising edge to CK alignment | +/- 0.25 tCK (+/- 0.27 at DDR3-1600 and above) |
| tWPRE / tWPST | Write DQS preamble / postamble | 0.9 min / 0.3 min tCK |
| tRPRE / tRPST | Read DQS preamble / postamble | 0.9 min / 0.3 min tCK |
| tDQSCK | Read DQS output access from CK (DLL window) | 400 ps max at 800, down to 180 ps at 2133 |
| tDQSQ | DQ skew against DQS, per group | 200 ps max at 800, down to 75 ps at 1866/2133 |
| tQH | DQ/DQS output hold from DQS | 0.38 tCK |
| tDS / tDH | Write DQ setup / hold against DQS, base values | AC150 / DC100 rows by speed (AC135 for 1866/2133); both derated by slew rate per 13.6.1 |

## Burst chop and interrupt rules

- BC4 (burst chop): a BL8 fetch truncated to 4 data words, selected by
  A12 at the command (on-the-fly) or fixed in MR0. tCCD between a BC4 and
  a following BC4 is 4 clocks; a chopped burst still pays the full fetch.
- BC4 bursts are never interruptible. BL8 bursts may only be cut by a
  same-direction burst aligned to the 4-word (BC4) boundary.
- There is no Burst Terminate command. A burst runs its full length
  unless legally interrupted as above.

**Source:** JESD79-3F sections 4.13, 4.14, 13.1 (Tables 68-69), 13.6.1
