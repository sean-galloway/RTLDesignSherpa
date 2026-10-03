# Organization

## Banks, rows, columns

A DDR2 device is a set of independent banks. Each bank is a 2D array
addressed by row then column. Activating a bank copies one row into that
bank's sense amplifiers (the "open row" or page); reads and writes then hit
the sense amps at column granularity. A bank must be precharged (closed)
before a different row in the same bank can be opened.

| Density | Banks | Bank address | Notes |
| --- | --- | --- | --- |
| 128 Mb | 4 | BA0-BA1 | x16 only |
| 256 Mb | 4 | BA0-BA1 | |
| 512 Mb | 4 | BA0-BA1 | |
| 1 Gb | 8 | BA0-BA2 | |
| 2 Gb | 8 | BA0-BA2 | |
| 4 Gb | 8 | BA0-BA2 | |

There are no bank groups in DDR2. All banks share one timing regime: tRRD
applies between any two Activates, tCCD between any two column commands,
and tFAW limits any rolling window of four Activates on 8-bank parts.

## Addressing

The row address rides with the Activate command on A0-A15 (width depends on
density). The column address rides with the Read or Write command; A10 is
not a column bit - it is the auto-precharge flag (often written AP). Column
addressing is A0-A9, plus A11 on x4 organizations, so a page holds 1024 or
2048 words.

Page size formula: page size = 2^COLBITS x ORG / 8 bytes, per bank.

| Density | Organization | Row bits | Column bits | Page size |
| --- | --- | --- | --- | --- |
| 1 Gb | x8 | A0-A13 | A0-A9 | 1 KB |
| 1 Gb | x16 | A0-A12 | A0-A9 | 2 KB |
| 2 Gb | x8 | A0-A14 | A0-A9 | 1 KB |
| 4 Gb | x16 | A0-A14 | A0-A9 | 2 KB |

## Prefetch and IO width

The 4n prefetch means one column access pulls 4 words per DQ pin group from
the array in parallel. Consequences:

- Minimum burst is 4 data words per pin (BL4); BL8 takes two internal
  4-word fetches.
- The array core runs at one quarter of the pin data rate.
- Internal read-to-precharge and write-recovery analog delays are defined
  from the last 4-word prefetch, which is why BL4 and BL8 sometimes get
  different formulas for the same parameter (tRTP is the classic case).

IO organizations are x4, x8 and x16, each with one DQS pair per 8 bits
(x4 shares one strobe per 4 bits).

## Ranks and stacked packages

The spec also covers dual-die and quad-die stacked packages. A stack
presents multiple ranks behind one channel: each rank gets its own chip
select (and its own ODT control), shares the address/command and data
busses, and is otherwise a complete independent DDR2 device. Rank-to-rank
traffic adds bus-turnaround constraints beyond single-rank rules.

## The drill model restated

This book's examples use 8 banks (B0-B7), 8 rows per bank (R0-R7) and 8
columns per row (C0-C7). One bank's state at a glance:

| Bank | State | Open row |
| --- | --- | --- |
| B0 | idle | - |
| B3 | active | R5 |
| B5 | active | R1 |

**Source:** JESD79-2F sections 2.2, 2.4, 3.2
