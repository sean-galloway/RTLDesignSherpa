# Organization

## Banks, rows, columns

An LPDDR4 channel is organized as eight independent banks of DRAM arrays. Each
bank has its own sense-amplifier row buffer, so up to eight rows can be open at
the same time within one channel. The bank count is always eight; the spec does
not define 4-bank LPDDR4 SDRAM devices.

Address geometry per density (from the spec addressing tables):

| Density | Channels | Banks | Rows (x16) | Columns | Page size (x16) |
| --- | --- | --- | --- | --- | --- |
| 2 Gb | 2 | 8 | R0-R12 | C0-C9 | 2048 B |
| 4 Gb | 2 | 8 | R0-R13 | C0-C9 | 2048 B |
| 6 Gb | 2 | 8 | R0-R14* | C0-C9 | 2048 B |
| 8 Gb | 2 | 8 | R0-R14 | C0-C9 | 2048 B |
| 12 Gb | 2 | 8 | R0-R15* | C0-C9 | 2048 B |
| 16 Gb | 2 | 8 | R0-R15 | C0-C9 | 2048 B |
| 24 Gb | 2 | 8 | R0-R16* | C0-C9 | 2048 B |
| 32 Gb | 2 | 8 | R0-R16 | C0-C9 | 2048 B |

*For non-binary densities, the top quarter of the row address space is invalid:
when the most-significant row address bit is high, the next bit must be low.

Single-channel dies carry the same per-channel geometry but only one channel;
dual-channel dies contain two independent copies of the table above. Byte-mode
(x8) parts halve the prefetch and page size while doubling the row count for the
same die density.

Addressing rules:

- The two least-significant column bits (C0-C1) are implied zero and are not
  transmitted on the CA bus. Column addresses on the bus start at C2.
- Unused row/column address bits on the CA bus must still be driven to valid
  logic levels.
- REFpb can only target a bank that is currently idle and precharged.

## Prefetch and IO width

- 16n prefetch: a column access fetches sixteen words per DQ internally. The
  DDR interface delivers two words per DQ per clock, so a BL16 burst occupies
  eight clocks. This is why tCCD = 8 clocks for BL16 and 16 clocks for BL32.
- Data bus widths are x16 and x8 (byte mode). Each byte lane has its own
  differential strobe (DQS_t/DQS_c) and its own DMI pin: one DQS pair and one
  DMI per 8 DQs.
- DMI replaces the older DM pin. It carries data-mask information for masked
  writes and data-bus-inversion status for reads and normal writes when DBIdc
  is enabled.

## Burst structure

Accesses are burst-oriented: each Read, Write or Masked Write command transfers
BL words per DQ, starting at the issued column and following the programmed
burst order. BL is normally 16; BL32 and on-the-fly BL16/BL32 are also
available. Burst addressing follows the standard sequential pattern driven by
the low-order column bits.

## Channels

A standard LPDDR4 die contains two fully independent channels (channel A and
channel B). Each channel has its own CA bus, clock, CKE, CS_n, ODT(ca), DQ,
DQS and DMI pins. The two channels share only package-level pins such as
RESET_n and ZQ. The protocol in this book is per-channel; the other channel
operates independently with the same rules.

## The simplified drill model

Per the Introduction, all examples use eight banks (B0-B7), eight rows (R0-R7)
and eight columns (C0-C7). Real parts are far larger; the small model exists to
make bank/row state obvious in command traces. A BL16 access wraps through the
eight-column model twice.

**Source:** JESD209-4E sections 2.1, 3.1
