# Organization

## Banks, rows, columns

An LPDDR2-SX device is organized as 4 or 8 banks of independent DRAM
arrays. Each bank has its own sense-amplifier row buffer, so up to 4 or 8
rows can be open simultaneously (one per bank). Density determines the
bank count: 64 Mb through 512 Mb parts have 4 banks, 1 Gb and larger
parts have 8 banks (S2/S4; check the addressing table for exact splits).

Address geometry per density (SDRAM, from the spec addressing table):

| Density | Banks | Rows | Columns (x16) | tREFI (us, <=85 C) |
| --- | --- | --- | --- | --- |
| 64 Mb | 4 | R0-R11 | C0-C7 | 15.6 |
| 128 Mb | 4 | R0-R11 | C0-C8 | 15.6 |
| 256 Mb | 4 | R0-R12 | C0-C8 | 7.8 |
| 512 Mb | 4 | R0-R12 | C0-C9 | 7.8 |
| 1 Gb | 4 (S2) / 8 (S4) | R0-R13 / R0-R12 | C0-C9 | 7.8 |
| 2 Gb | 4 (S2) / 8 (S4) | R0-R14 / R0-R13 | C0-C9 | 3.9 |
| 4 Gb | 8 | R0-R13 | C0-C10 | 3.9 |
| 6 Gb | 8 | R0-R14 | C0-C10 | 3.9 |
| 8 Gb | 8 | R0-R14 | C0-C10 | 3.9 |

x8 parts gain one column bit, x32 parts lose one, relative to x16.

Two addressing rules to remember:

- C0 is never transmitted on the CA bus; it is implied zero. Column
  addresses on the bus start at C1.
- 6 Gb parts have no memory where R13 and R14 are both high; an ACT or
  write to that space is ignored.

## Prefetch and IO width

- S4: 4n prefetch. A column access fetches 4 words per DQ internally;
  the interface delivers 2 words per DQ per clock (DDR), so a minimum
  burst occupies 2 clocks. This is why tCCD = 2 clocks on S4.
- S2: 2n prefetch, 1 clock minimum per burst, tCCD = 1 clock.

Data bus widths are x8, x16 and x32. Each byte lane has its own
differential strobe (DQS_t/DQS_c) and its own DM mask pin: one DQS pair
and one DM per 8 DQs.

## Burst structure

Accesses are burst-oriented: one Read or Write command moves BL words
per DQ, starting at the issued column and following the programmed
burst order (sequential or interleaved, wrap or no-wrap). BL is 4, 8 or
16, programmed in MR1.

## Channels

Multi-channel parts exist at the package level: a PoP package can carry
two fully independent LPDDR2 channels (each with its own CA bus, clock,
CKE and CS_n). Channels share nothing but the package; the protocol in
this book is per-channel.

## The simplified drill model

Per Chapter 1, all examples use 8 banks (B0-B7), 8 rows (R0-R7) and 8
columns (C0-C7). Real parts are far larger; the small model exists to
make bank/row state obvious in command traces.

**Source:** JESD209-2F sections 2.13 (Table 3), 3
