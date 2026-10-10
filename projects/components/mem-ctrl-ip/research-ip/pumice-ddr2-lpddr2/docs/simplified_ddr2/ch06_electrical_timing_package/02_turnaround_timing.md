# Turnaround and Burst Timing

Column-command spacing and bus-direction rules. These are the parameters
that decide how full the DQ bus can be kept.

## CAS-to-CAS and latencies

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tCCD | Column command to column command, same or different banks | RD/WR -> RD/WR (any direction same-type) | 2 clocks |
| RL | Read latency: command to first data | RD -> first DQS/DQ out | AL + CL clocks |
| WL | Write latency: command to first strobe | WR -> first DQS in | RL - 1 clocks |
| CL | CAS latency component of RL | posted internal CAS -> data | 2-6 clocks (MR) |
| AL | Additive latency: posted-CAS hold | RD/WR command -> internal CAS | 0-4 clocks, 5 optional (EMR1) |

BL/2 clocks of bus occupancy per burst: BL4 occupies 2 clocks of DQ, BL8
occupies 4. Seamless same-direction traffic means issuing a command every
BL/2 clocks - at BL4 that is exactly tCCD = 2, so back-to-back BL4 bursts
saturate the bus.

## Direction changes

Note on tRTW: JESD79-2F specifies the read-to-write spacing directly as a
relation (BL/2 + 2 clocks, section 3.6.3) without assigning it a symbol.
This book calls it tRTW because the other specifications in this series
(LPDDR3/4, DDR3/4/5, HBM) name that parameter, and a common symbol set
keeps the timing tables comparable across books.

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tRTW | Read-to-write turnaround: read burst and postamble must clear before write preamble (book symbol; the spec gives the relation unnamed) | RD(any bank) -> WR(any bank) | BL/2 + 2 clocks: 4 at BL4, 6 at BL8 |
| tWTR | Write-to-read: last write data must propagate from input buffer into the sense amps | end of WR burst(any) -> RD(any) | 7.5 ns (10 ns at DDR2-400) |

Command-spacing forms:

| Transition | Spacing from first command (clocks) |
| --- | --- |
| RD -> WR | BL/2 + 2 |
| WR -> RD | CL - 1 + BL/2 + RU(tWTR) |
| RD -> RD | max(tCCD, BL/2) |
| WR -> WR | max(tCCD, BL/2) |

Worked example (the Chapter 4 configuration: CL=3, AL=2, RL=5, WL=4,
BL4, tWTR=3 clk): RD->WR = 4 clocks, WR->RD = 2+2+3 = 7 clocks. The
asymmetry is the write path's longer internal tail; reads turn into writes
cheaper than writes into reads.

## Strobe-level timing (for completeness)

These bound the DQS/DQ relationship rather than the scheduler, but the
controller's PHY must meet them:

| Symbol | Definition | Value |
| --- | --- | --- |
| tDQSS | Write DQS latching edge to CK alignment | +/- 0.25 tCK |
| tWPRE / tWPST | Write DQS preamble / postamble | 0.35 min / 0.4-0.6 tCK |
| tRPRE / tRPST | Read DQS preamble / postamble | 0.9-1.1 / 0.4-0.6 tCK |
| tDQSCK | Read DQS output access from CK (DLL window) | +/- 350-500 ps by bin |
| tDQSQ | DQ skew against DQS | 200-350 ps by bin |
| tQH | DQ/DQS output hold from DQS | tHP - tQHS |
| tDS / tDH | Write DQ setup / hold against DQS | bin-dependent, 50-275 ps base |

## Burst interrupt rules

- BL4: never interruptible, in either direction, by anything.
- BL8: a read may be cut by a later read, or a write by a later write, at
  the 4-word (prefetch) boundary only. The new command's data follows
  seamlessly.
- There is no Burst Terminate command. A burst always runs its full
  length unless legally interrupted as above.

**Source:** JESD79-2F sections 3.6.1-3.6.4, Tables 42-43
