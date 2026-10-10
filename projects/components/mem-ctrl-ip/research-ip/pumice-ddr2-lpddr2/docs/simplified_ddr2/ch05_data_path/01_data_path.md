# Data Path: Prefetch, Bursts, Strobes

## 4n prefetch

Every column access moves 4 words per IO group between the array and the
IO buffers at once. The array core therefore runs at one quarter of the
pin data rate, which is the fundamental trick that let DDR2 double DDR's
bus speed without a proportionally faster core.

Consequences that show up everywhere else in the spec:

- BL4 is the minimum burst; BL8 takes two consecutive 4-word internal
  fetches.
- Analog delays tied to data movement (tRTP, tWTR, tWR) are defined from
  the last 4-word prefetch, not from the command - which is why BL4 and
  BL8 versions of the same rule differ by 2 clocks.
- Burst interrupts, where legal at all, are only legal on 4-word
  boundaries (the prefetch granularity).

## Burst length and burst order

BL is 4 or 8, set in MR. Burst type (MR A3) picks the address sequence
within the burst:

| BL | Start A1A0 | Sequential | Interleaved |
| --- | --- | --- | --- |
| 4 | 00 | 0,1,2,3 | 0,1,2,3 |
| 4 | 01 | 1,2,3,0 | 1,0,3,2 |
| 4 | 10 | 2,3,0,1 | 2,3,0,1 |
| 4 | 11 | 3,0,1,2 | 3,2,1,0 |

BL8 follows the same wrap-and-pair-swap pattern over A2-A0 (sequential
wraps in 4-word nibbles; interleaved swaps adjacent pairs within each
nibble). Sequential mode at BL8 is nibble-based: the low 4 words wrap
within their aligned 4-word group before the upper 4.

The practical use of interleaved order: a critical-word-first cache-line
fill, where the requested word arrives first and the rest of the line
follows in pair-swapped order.

## DQS: the source-synchronous strobe

DQ data is not referenced to CK at the pin; it is referenced to DQS.

- Reads: the DRAM drives DQS edge-aligned with DQ. DQS drops low one clock
  before the first data (read preamble, tRPRE ~ 0.9-1.1 tCK) and returns
  to tri-state after a postamble (tRPST). tDQSCK bounds DQS against CK
  (DLL-controlled), tDQSQ bounds DQ skew against DQS, tQH the hold.
- Writes: the controller drives DQS roughly center-aligned to each DQ
  window. DQS must arrive aligned to CK within tDQSS (+/- 0.25 tCK); setup
  and hold of DQ against DQS are tDS/tDH. Write preamble tWPRE and
  postamble tWPST frame the burst.
- DQS is normally differential (DQS/DQS#). Single-ended mode (EMR1 A10)
  exists; the complement pin must then be tied off externally.

## Write data mask (DM)

One DM pin per byte lane, sampled with write data: high masks that byte
(the cell keeps its old value). No read masking. On x8 parts, enabling
RDQS (EMR1 A11) repurposes the DM pin as a read strobe echo - masking is
lost, so partial writes become read-modify-write at the controller.

## Latency arithmetic, collected

| Quantity | Formula | Programmed by |
| --- | --- | --- |
| RL (read latency) | AL + CL | EMR1 (AL), MR (CL) |
| WL (write latency) | RL - 1 | derived |
| RD cmd -> data | RL clocks | |
| WR cmd -> first DQS | WL clocks | |
| RD -> RD, WR -> WR | max(tCCD=2, BL/2) | |

**Source:** JESD79-2F sections 3.6, 3.6.1-3.6.5
