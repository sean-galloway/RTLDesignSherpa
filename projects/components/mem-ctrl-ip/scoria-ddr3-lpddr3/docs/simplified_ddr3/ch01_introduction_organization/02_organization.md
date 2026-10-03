# Organization

## Banks, rows, columns

A DDR3 device is a flat set of eight independent banks. Each bank is a
2D array addressed by row then column. An Activate command copies one row into
that bank's sense amplifiers (the open row or page); reads and writes then hit
the sense amplifiers at column granularity. A bank must be precharged before a
different row in the same bank can be opened.

All standard densities use eight banks selected by BA0-BA2:

| Density | Org | Row address | Column address | Page size |
| --- | --- | --- | --- | --- |
| 512 Mb | x8 | A0-A12 | A0-A9 | 1 KB |
| 512 Mb | x16 | A0-A11 | A0-A9 | 2 KB |
| 1 Gb | x8 | A0-A13 | A0-A9 | 1 KB |
| 1 Gb | x16 | A0-A12 | A0-A9 | 2 KB |
| 2 Gb | x8 | A0-A14 | A0-A9 | 1 KB |
| 4 Gb | x16 | A0-A14 | A0-A9 | 2 KB |
| 8 Gb | x8 | A0-A15 | A0-A9, A11 | 2 KB |

There are no bank groups in DDR3. All banks share one timing regime: tRRD
applies between any two Activates, tCCD between any two column commands, and
tFAW limits any rolling window of four Activates.

## Addressing

The row address is supplied with the Activate command on A0-A15 (the exact
width depends on density). The column address is supplied with the Read or
Write command. A10 is not a column bit; it is the auto-precharge flag (AP).
A12/BC# chooses between BL8 and BC4 on-the-fly during a column command when
OTF is enabled; otherwise the burst mode is fixed in the mode register.

Page size formula: page size = 2^COLBITS x ORG / 8 bytes, per bank.
The extra column address bits used on x4 and some x8 densities (A11, and A13
on 8 Gb x4) keep the per-bank page at either 1 KB or 2 KB.

## Prefetch and IO width

The 8n prefetch means one column access pulls eight words per DQ pin group
from the array in parallel. Consequences:

- The smallest useful burst is four data words per pin (BC4); BL8 uses the
  full eight-word fetch.
- The array core runs at one eighth of the pin data rate.
- A BC4 burst transfers the first four words of the prefetch and discards the
  second four.

IO organizations are x4, x8 and x16. x4 uses one DQS pair for four DQ pins;
x8 uses one DQS pair for eight DQ pins; x16 has two DQS pairs, one for each
byte lane. x8 parts also support an optional termination data strobe pair,
TDQS/TDQS#, when enabled in MR1.

## Ranks and stacked packages

The spec covers single-die, dual-die and quad-die packages. A stacked package
presents multiple ranks behind one channel: each rank gets its own chip select
(and its own ODT and CKE in multi-rank ballouts), shares the address/command
and data busses, and is otherwise a complete independent DDR3 device.
Rank-to-rank traffic adds bus-turnaround constraints beyond single-rank rules.

## The drill model restated

This book's examples use eight banks (B0-B7), eight rows per bank (R0-R7) and
eight columns per row (C0-C7). One bank's state at a glance:

| Bank | State | Open row |
| --- | --- | --- |
| B0 | idle | - |
| B3 | active | R5 |
| B5 | active | R1 |

**Source:** JESD79-3F sections 2.10, 2.11, 3.2
