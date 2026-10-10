# Data Path

## Prefetch and burst

LPDDR3 uses an 8n prefetch: each column access moves eight bits per DQ
between the array and the IO, serialized as four UI on each of two clock
cycles. The fixed burst length is BL8. There is no burst chop and no
interleaved burst type; every column transaction delivers eight consecutive
column locations starting from the commanded column address.

## Read and write strobes

A single bidirectional differential pair (DQS_t/DQS_c) serves each byte lane.

| Direction | Driver | Alignment | Preamble | Postamble |
| --- | --- | --- | --- | --- |
| Read | DRAM | Edge-aligned to DQ | tRPRE >= 0.9 tCK | tRPST >= 0.3 tCK |
| Write | Controller | Centered in DQ eye | tWPRE >= 0.8 tCK | tWPST >= 0.4 tCK |

There is no DLL. The read strobe is timed with a wide access window rather
than a locked phase: tDQSCK ranges from 2.5 ns (min) to 5.5 ns (max). The
controller must train its capture logic to absorb this spread, using the
MR32/MR40 DQ calibration patterns and the normal read eye.

## Read and write latencies

RL and WL are programmed through MR2. Two WL sets (A and B) trade extra write
latency for easier system timing at the higher speeds.

| MR2 OP<3:0> | RL | WL Set A | WL Set B | Max CK freq |
| --- | --- | --- | --- | --- |
| 0001B | 3 | 1 | 1 | <= 166 MHz (optional) |
| 0100B | 6 | 3 | 3 | <= 400 MHz |
| 0110B | 8 | 4 | 4 | <= 533 MHz |
| 0111B | 9 | 5 | 5 | <= 600 MHz |
| 1000B | 10 | 6 | 8 | <= 667 MHz (default) |
| 1001B | 11 | 6 | 9 | <= 733 MHz |
| 1010B | 12 | 6 | 9 | <= 800 MHz |
| 1100B | 14 | 8 | 11 | <= 933 MHz |
| 1110B | 16 | 8 | 13 | <= 1066 MHz |

| Symbol | Timing relationship |
| --- | --- |
| tDQSCK | CK edge to first valid DQS edge: 2.5 ns min, 5.5 ns max |
| tDQSQ | DQS-to-DQ skew: max 165/135/115/100 ps at 1333/1600/1866/2133 MT/s |
| RD cmd -> first DQ | RL x tCK + tDQSCK + tDQSQ |
| WR cmd -> first DQS | WL x tCK + tDQSS |
| tDQSS | WR cmd CK edge to first DQS latching edge: 0.75-1.25 tCK |
| tDQSH / tDQSL | DQS high/low pulse width during writes: >= 0.4 tCK |
| tDSS / tDSH | DQS falling edge setup/hold to CK: >= 0.2 tCK |
| tDS / tDH | DQ/DM setup/hold to DQS: 175/150/130/115 ps at 1333/1600/1866/2133 |

| Symbol | Turnaround relationship |
| --- | --- |
| tCCD | CAS-to-CAS delay: 4 tCK |
| tWTR | WR -> RD: max(7.5 ns, 4 tCK), measured from the CK edge after the last write datum |
| tRTW (book symbol) | RD -> WR: RL + RU(tDQSCK(MAX)/tCK) + BL/2 + 1 - WL clock cycles. JESD209-3C does not name this symbol; it is the cross-book convention. |

## DM - write data mask

One DM pin per byte lane is sampled on both DQS edges with the write data.
When DM is high for a beat, that byte is masked and not written. DM loading
matches DQ/DQS loading so timing tracks the data. Partial writes (e.g. AXI W
with sparse WSTRB) can use DM instead of a read-modify-write.

## What LPDDR3 does not have

- No data bus inversion (DBI) on reads or writes.
- No parity on the CA bus and no CRC on the data bus.
- No on-die ECC.
- No burst chop, no interleaved burst order, and no additive latency.

Every DQ cycle carries payload; the controller must provide any error
protection.

## Signaling

The DQ/DQS/DM interface is HSUL_12: 1.2 V VDDQ (nominal 1.20 V, min 1.14 V,
max 1.30 V), with VREFDQ near VDDQ/2 at the receiver. Unlike LPDDR2,
LPDDR3 adds a dedicated ODT pin and programmable on-die termination for the
data bus; termination is asynchronous and is covered in the next file.

**Source:** JESD209-3C sections 3.4.1 (MR1, MR2), 4.3, 4.4, 4.5, 4.6, 4.10.2,
4.11.2, 8.6.1, Table 64
