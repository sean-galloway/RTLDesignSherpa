# Turnaround and Burst Timing

Column-command spacing and bus-direction rules, now bank-group aware.

## Latencies and CAS-to-CAS

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tCCD_S | Column command to column command, DIFFERENT bank groups | RD/WR -> RD/WR (any type, cross-group) | 4 nCK (constant across bins) |
| tCCD_L | Column command to column command, SAME bank group | RD/WR -> RD/WR (any type, same group) | 5-8 nCK by speed |
| RL | Read latency | RD -> first data | AL + CL; CL 10-24, AL 0 / CL-1 / CL-2 (MR1) |
| WL | Write latency | WR -> first DQS | AL + CWL; CWL 9-20 paired per speed bin |

BL8 occupies 4 clocks of DQ. Cross-group same-direction traffic issues a
column command every tCCD_S = 4 clocks - exactly BL/2, so interleaving
two bank groups saturates the bus. Same-group traffic pays tCCD_L, so a
single-group stream cannot fill the bus no matter how many banks it has:
the group, not the bank, is the scheduling quantum.

## Direction changes

Note on tRTW: JESD79-4D does not name the read-to-write parameter (the
symbol does not appear in the spec). It gives the relation in the write
timing material: RBL/2 + 1 tCK + tWPRE plus the latency offset (CL -
CWL, or RL - WL when AL is set). This book calls the parameter tRTW,
matching the other books.

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tRTW | Read-to-write turnaround: read burst and postamble must clear before the write preamble (book symbol; relation unnamed in the spec) | RD(any) -> WR(any) | RL - WL + BL/2 + 1 + RU(tWPRE) |
| tWTR_S | Write-to-read, different bank groups | last write data -> internal RD (cross-group) | max(2 nCK, 2.5 ns): 2-4 nCK by speed |
| tWTR_L | Write-to-read, same bank group | last write data -> internal RD (same group) | max(4 nCK, 7.5 ns): 6-12 nCK by speed |

Command-spacing forms (from the WR command):

| Transition | Spacing (clocks) |
| --- | --- |
| RD -> WR | RL - WL + BL/2 + 1 + RU(tWPRE) |
| WR -> RD | WL + BL/2 + RU(tWTR_S) cross-group; WL + BL/2 + RU(tWTR_L) same-group |
| RD -> RD / WR -> WR | max(tCCD_S, BL/2) cross-group; tCCD_L same-group |

Worked example (the Chapter 4 configuration: CL = CWL = 10, AL = 0, so
RL = WL = 10; BL8; tWPRE = 1 tCK; tWTR_S = 2, tWTR_L = 4): RD->WR =
10 - 10 + 4 + 1 + 1 = 6 clocks. WR->RD = 10 + 4 + 2 = 16 clocks
cross-group (18 same-group). The group split applies to the write tail
exactly where it applies to column spacing - same-group writes into
reads are the most expensive transition in the book.

Write CRC stretches the frame: with CRC enabled the write carries an
extra CRC beat, write recovery and tWTR reference points move to the CRC
field (tWR_CRC_DM), and the write latency may gain a clock - see the
data-path chapter.

## Strobe-level notes

- Read preamble is programmable (MR4): 1 tCK or 2 tCK - the 2 tCK
  setting relaxes the DQS/CK alignment budget on loaded boards.
- Postamble and write preamble values are per the AC tables; tWPRE is
  the value that appears in the tRTW relation above.
- tDQSCK stays DLL-tight (the DLL is mandatory in normal operation);
  DQS-to-DQ skew tDQSQ and hold tQH are per the speed-bin tables.

**Source:** JESD79-4D sections 4.19, 4.24, 4.25, 13 (AC tables)
