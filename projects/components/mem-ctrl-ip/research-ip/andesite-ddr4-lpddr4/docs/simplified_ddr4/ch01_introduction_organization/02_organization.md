# Organization

## Banks, rows, columns

A DDR4 device is organized as one or more bank groups, and each bank group
contains four independent banks. Each bank is a 2D array addressed by row then
column. An Activate command copies one row into that bank's sense amplifiers
(the open row or page); reads and writes then hit the sense amplifiers at
column granularity. A bank must be precharged before a different row in the
same bank can be opened.

Addressing choices by density and IO width:

| Density | Org | Bank groups | Banks per group | Row address | Column address | Page size |
| --- | --- | --- | --- | --- | --- | --- |
| 2 Gb | x4 | 4 | 4 | A0-A14 | A0-A9 | 512 B |
| 2 Gb | x8 | 4 | 4 | A0-A13 | A0-A9 | 1 KB |
| 2 Gb | x16 | 2 | 4 | A0-A13 | A0-A9 | 2 KB |
| 4 Gb | x4 | 4 | 4 | A0-A15 | A0-A9 | 512 B |
| 4 Gb | x8 | 4 | 4 | A0-A14 | A0-A9 | 1 KB |
| 4 Gb | x16 | 2 | 4 | A0-A14 | A0-A9 | 2 KB |
| 8 Gb | x4 | 4 | 4 | A0-A16 | A0-A9 | 512 B |
| 8 Gb | x8 | 4 | 4 | A0-A15 | A0-A9 | 1 KB |
| 8 Gb | x16 | 2 | 4 | A0-A15 | A0-A9 | 2 KB |
| 16 Gb | x4 | 4 | 4 | A0-A17 | A0-A9 | 512 B |
| 16 Gb | x8 | 4 | 4 | A0-A16 | A0-A9 | 1 KB |
| 16 Gb | x16 | 2 | 4 | A0-A16 | A0-A9 | 2 KB |

The two bank-address pins (BA0-BA1) select the bank inside a group; the bank-
group pins (BG0-BG1 for x4/x8, BG0 for x16) select the group.

## Pinout highlights versus DDR3

The command/address bus was reorganized and several new pins appeared:

| Pin | Role |
| --- | --- |
| ACT_n | Activation command input; when low, RAS_n/A16, CAS_n/A15, WE_n/A14 carry row-address bits |
| BG0-BG1 | Bank-group selection (x4/x8 have both; x16 has only BG0) |
| PAR | Even-parity input for the command/address bus |
| ALERT_n | Active-low alert output for CRC/parity errors; also a connectivity-test input |
| VPP | 2.5 V activating (wordline) supply, in addition to 1.2 V VDD/VDDQ |
| TEN | Connectivity-test mode enable (required on x16, optional on x4/x8 8 Gb and above) |

## Bank group timing split

Because banks in different groups can operate more independently, several
timing parameters have short and long forms:

| Symbol | Applies between |
| --- | --- |
| tCCD_S | Consecutive column commands to different bank groups |
| tCCD_L | Consecutive column commands to the same bank group |
| tRRD_S | Consecutive Activate commands to different bank groups |
| tRRD_L | Consecutive Activate commands to different banks in the same group |
| tWTR_S | Write followed by read to a different bank group |
| tWTR_L | Write followed by read to the same bank group |

tFAW still limits any rolling window of four Activates.

## Addressing

The row address is supplied with the Activate command on A0-A17 (the exact
width depends on density and organization). The column address is supplied
with the Read or Write command. A10 is not a column bit; it is the auto-
precharge flag (AP). A12/BC_n chooses between BL8 and BC4 on-the-fly during a
column command when OTF is enabled; otherwise the burst mode is fixed in the
mode register.

Page size formula: page size = 2^COLBITS x ORG / 8 bytes, per bank. Wider
organizations use fewer column bits to keep the per-bank page at roughly 512 B
(x4), 1 KB (x8), or 2 KB (x16).

## Prefetch and IO width

The 8n prefetch means one column access pulls eight words per DQ pin group
from the array in parallel. Consequences:

- The smallest useful burst is four data words per pin (BC4); BL8 uses the
full eight-word fetch.
- The array core runs at one eighth of the pin data rate.
- A BC4 burst transfers the first four words of the prefetch and discards the
second four.

IO organizations are x4, x8, and x16. x4 uses one DQS pair for four DQ pins;
x8 uses one DQS pair for eight DQ pins; x16 has two DQS pairs, one for each
byte lane. x8 parts also support an optional termination data strobe pair,
TDQS/TDQS#, when enabled in MR1. A non-standard x32 ballout is also described
for specialized packages.

## Ranks and stacked packages

The spec covers single-die, dual-die, and quad-die packages. A stacked package
presents multiple ranks behind one channel: each rank gets its own chip select
(and its own ODT and CKE in multi-rank ballouts), shares the address/command
and data busses, and is otherwise a complete independent DDR4 device.
Rank-to-rank traffic adds bus-turnaround constraints beyond single-rank rules.

## The drill model restated

This book's examples use two bank groups (BG0 and BG1), four banks per group
(B0-B3 in BG0, B4-B7 in BG1), eight rows per bank (R0-R7), and eight columns
per row (C0-C7). One bank's state at a glance:

| Bank | State | Open row |
| --- | --- | --- |
| B0 | idle | - |
| B5 | active | R1 |

**Source:** JESD79-4D sections 2.7, 2.8, 2.9, 3.2
