# Turnaround and Burst Timing

Column-command spacing and bus-direction rules. LPDDR4 is the first book
in this series whose spec NAMES the read-to-write parameter: tRTW
appears in the MPC/WDQS timing material.

## Latencies and CAS-to-CAS

Read and write latency are programmed (no DLL), chosen per clock
frequency from the latency tables, with separate columns for read DBI
(+2 clocks when read DBI is enabled above the lowest rates) and two
write-latency sets (MR2 OP6):

| Symbol | Definition | Value |
| --- | --- | --- |
| RL | Read latency, command to first data | 6-36 nCK by frequency (10 at 266-533 MHz, 36 at 1866-2133 MHz; x8 mode runs higher) |
| WL | Write latency, command to first DQS | set A 4-18 nCK, set B 4-34 nCK, by frequency |
| nWR / nRTP | Programmed write-recovery / read-to-precharge clocks for auto-precharge | from the same table (RU of tWR/tRTP) |
| tCCD | Column command to column command | 8 tCK (BL16); BL32 adds another 8 |

BL16 occupies 8 clocks of DQ - a much longer bus reservation than the
DDR4-style 4. Seamless same-direction traffic issues a column command
every 8 clocks, which is exactly tCCD. Burst interrupts are not allowed;
BL32 may be selected on the fly for either direction.

## Direction changes

| Symbol | Definition | Value |
| --- | --- | --- |
| tRTW | Read-to-write turnaround (NAMED in JESD209-4E): the loose read strobe (no DLL) plus the burst must clear before the write preamble | command gap = RL + RU(tDQSCK(MAX)/tCK) + BL/2 - WL + tWPRE + RU(tRPST); tRTW also appears in the MPC/WDQS timing table |
| tWTR | Write-to-read: last write data into the array before a read | max(10 ns, 8 nCK) x16; max(12 ns, 8 nCK) x8 |

Command-spacing forms (drill numbers in the Chapter 4 configuration:
RL = 10, WL = 6, BL16, tWTR = 6 clk, tDQSCK(MAX) = 2 clk, tWPRE = 2
tCK, tRPST = 0.5 tCK):

| Transition | Spacing (clocks) | Drill value |
| --- | --- | --- |
| RD -> WR | RL + RU(tDQSCK(MAX)/tCK) + BL/2 - WL + tWPRE + RU(tRPST) | 10 + 2 + 8 - 6 + 2 + 1 = 16 (the 0.5 nCK postamble rounds up) |
| WR -> RD | WL + 1 + BL/2 + RU(tWTR/tCK) | 6 + 1 + 8 + 6 = 21 |
| RD -> RD / WR -> WR | max(tCCD, BL/2) = 8 | 8 |

The no-DLL tDQSCK term is why tRTW is named and tabled in this spec:
the controller must budget the worst-case strobe wander, not a locked
skew. WDQS control (see the data-path chapter) can gate DQS drive
between bursts, but its on/off constraints are checked against tRTW
when ODT is disabled - the turnaround rules still win.

## Strobe-level notes

- Read preamble: 2 tCK, static (no-toggle) or toggling per MR.
- Read postamble: 0.5 tCK standard, 1.5 tCK extended per MR.
- Write preamble 2 tCK; write postamble per the AC tables.
- tDQSCK: 1.5-3.5 ns min/max window (the value inside tRTW above);
  tDQSQ max 0.18 UI.
- DMI carries the mask (DM) and the DBI flag per byte lane; read DBI
  costs +2 RL clocks at the higher rates.

**Source:** JESD209-4E sections 4.5-4.13, 4.35 (MPC/WDQS timing), 10 (AC tables)
