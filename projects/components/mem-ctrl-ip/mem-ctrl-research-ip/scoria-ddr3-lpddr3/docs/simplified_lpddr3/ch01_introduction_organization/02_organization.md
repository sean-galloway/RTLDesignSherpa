# Organization

## Banks, rows, columns

An LPDDR3 device is organized as eight independent banks of DRAM arrays.
Each bank has its own sense-amplifier row buffer, so up to eight rows can
be open at the same time (one per bank). The bank count is always eight;
the spec does not define 4-bank LPDDR3 SDRAM devices.

Address geometry per density (from the spec addressing table):

| Density | Banks | Rows (x16) | Columns (x16) | tREFI (us, <=85 C) |
| --- | --- | --- | --- | --- |
| 1 Gb | 8 | R0-R12 | C0-C9 | 7.8 |
| 2 Gb | 8 | R0-R13 | C0-C9 | 3.9 |
| 4 Gb | 8 | R0-R13 | C0-C10 | 3.9 |
| 6 Gb | 8 | R0-R14* | C0-C10 | 3.9 |
| 8 Gb | 8 | R0-R14* | C0-C10 | 3.9 |
| 12 Gb | 8 | R0-R14* | C0-C11 | 3.9 |
| 16 Gb | 8 | R0-R14* | C0-C11 | 3.9 |
| 32 Gb | 8 | TBD | TBD | TBD |

*Addresses with R13 and R14 both high have no memory; an ACT to that
space is ignored.

x32 parts lose one column address bit relative to x16; x16 parts expose
one more column bit than x32 at the same density.

Addressing rules:

- The least-significant column bit C0 is implied zero and does not
  appear on the CA bus. Column addresses on the bus start at C1.
- REFpb can only target a bank that is currently idle and precharged.

## Prefetch and IO width

- 8n prefetch: a column access fetches eight words per DQ internally. The
  DDR interface delivers two words per DQ per clock, so a minimum burst
  occupies four clocks. This is why tCCD = 4 clocks on LPDDR3.
- Data bus widths are x16 and x32. Each byte lane has its own
  differential strobe (DQS_t/DQS_c) and its own DM mask pin: one DQS pair
  and one DM per 8 DQs.

## Burst structure

Accesses are burst-oriented: each Read or Write command transfers BL
words per DQ, starting at the issued column and following the programmed
burst order. BL is fixed at 8. Burst addressing follows the standard sequential
pattern driven by the low-order column bits.

## Channels

Multi-channel parts exist at the package level: a PoP or discrete package
can carry two fully independent LPDDR3 channels, each with its own CA
bus, clock, CKE and CS_n. Channels share nothing but the package; the
protocol in this book is per-channel.

## The simplified drill model

Per the Introduction, all examples use eight banks (B0-B7), eight rows
(R0-R7) and eight columns (C0-C7). Real parts are far larger; the small
model exists to make bank/row state obvious in command traces.

**Source:** JESD209-3C sections 2.1-2.3, 3.1
