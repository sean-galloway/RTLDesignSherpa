# Data Path

## Prefetch and burst

LPDDR4 uses a 16n prefetch: each column access moves sixteen bits per DQ
between the array and the IO, serialized as eight UI across two clock cycles.
The default burst length is BL16. MR1 OP[1:0] can also select BL32 or
BL16/32 on-the-fly, but there is no burst chop and no interleaved burst type.
For reads, C[1:0] are implied zero, so the start column is always a multiple of
four. For writes, C[3:2] must be driven low and the start address is aligned to
the prefetch boundary (16n for BL16, 32n for BL32). In the drill model, BL16
delivers the eight columns C0-C7 twice.

## Read and write strobes

One bidirectional differential pair (DQS_t/DQS_c) serves each byte lane. The
DRAM drives it during reads and the controller drives it during writes.

| Direction | Driver | Alignment | Preamble | Postamble |
| --- | --- | --- | --- | --- |
| Read | DRAM | Edge-aligned to DQ | 2 tCK (static or toggle) | 0.5 tCK or 1.5 tCK |
| Write | Controller | Centered in DQ eye | 2 tCK required | 0.5 tCK or 1.5 tCK |

Minimum preamble width is 1.8 tCK. The standard postamble is at least 0.4 tCK;
the extended postamble is at least 1.4 tCK. There is no DLL. The read strobe
access window is wide: tDQSCK spans 1.5 ns to 3.5 ns, with up to 4 ps/C and
7 ps/mV drift. The controller must train its capture logic to absorb this
spread. DQS-to-DQ skew tDQSQ is at most 0.18 UI.

| Symbol | Definition |
| --- | --- |
| tDQSCK | CK edge to first valid DQS edge: 1.5 ns min, 3.5 ns max |
| tDQSQ | DQS-to-DQ skew: max 0.18 UI |
| RD cmd -> first DQ | RL x tCK + tDQSCK + tDQSQ |
| WR cmd -> first DQS latching edge | WL x tCK + tDQSS |
| tDQSS | WR cmd CK edge to first DQS latching edge: 0.75-1.25 tCK |
| tDQS2DQ | DQS must arrive at DRAM before DQ by this trained offset |
| tDQSH / tDQSL | DQS high/low pulse width during writes: >= 0.4 tCK |
| tDSS / tDSH | DQS falling edge setup/hold to CK: >= 0.2 tCK |

## Read and write latencies

RL and WL are programmed through MR2. Two write-latency sets (A and B) trade
extra latency for easier system timing at higher speeds; MR2 OP[6] selects the
set. Enabling read DBI (MR3 OP[6]) adds two clocks to RL.

| RL (no DBI / with DBI) | WL Set A | WL Set B | nWR | nRTP | Max CK freq |
| --- | --- | --- | --- | --- | --- |
| 6 / 6 | 4 | 4 | 6 | 8 | <= 266 MHz |
| 10 / 12 | 6 | 8 | 10 | 8 | <= 533 MHz |
| 14 / 16 | 8 | 12 | 16 | 8 | <= 800 MHz |
| 20 / 22 | 10 | 18 | 20 | 8 | <= 1066 MHz |
| 24 / 28 | 12 | 22 | 24 | 10 | <= 1333 MHz |
| 28 / 32 | 14 | 26 | 30 | 12 | <= 1600 MHz |
| 32 / 36 | 16 | 30 | 34 | 14 | <= 1866 MHz |
| 36 / 40 | 18 | 34 | 40 | 16 | <= 2133 MHz |

The table above is for x16 mode; x8 byte mode uses slightly different codes.

| Symbol | Turnaround relationship |
| --- | --- |
| tCCD | CAS-to-CAS delay: 8 tCK for BL16, 16 tCK for BL32 |
| tWTR | WR -> RD: max(10 ns, 8 tCK), measured from the CK edge after the last write datum |
| tRTW | RD -> WR depends on DQ ODT state. With DQ ODT disabled: RL + RU(tDQSCK(max)/tCK) + BL/2 - WL + tWPRE + RD(tRPST). With DQ ODT enabled: RL + RU(tDQSCK(max)/tCK) + BL/2 + RD(tRPST) - ODTLon - RD(tODTon,min/tCK) + 1. |

## WDQS control

Before and after writes the differential DQS must keep enough voltage
separation to keep the write receivers out of metastability. LPDDR4 offers two
ways to manage this:

- Mode 1 (read-based): the SoC leaves DQS_c high except during read bursts,
  write bursts, and RD/WT turnarounds.
- Mode 2 (WDQS_on/off): after a Write-1 or Masked Write-1 command, DQS_t/DQS_c
  must be differential by WDQS_on (max) and can return to a don't-care state
  after WDQS_off (min). These windows vary by WL set and frequency; overlap
  with read bursts or turnarounds is ignored.

Both modes cut DQS toggling to save power without changing normal command
spacing.

## Masked write, DM, and DBI

LPDDR4 has no dedicated DM pin. Each byte lane has a bidirectional DMI pin
sampled with the DQ on both edges. What DMI carries depends on the operation
and mode-register settings.

| Function | MR bits | DMI meaning |
| --- | --- | --- |
| Data mask for masked writes | MR13 OP[5] = 0, use Masked Write command | DMI high -> mask this beat; low -> write normally |
| Write DBI | MR3 OP[7] = 1 | DMI high -> invert received DQ byte; low -> leave it |
| Read DBI | MR3 OP[6] = 1 | DRAM drives DMI high when it inverts a read byte (more than four ones in the byte) |

A Masked Write command is mandatory whenever any beat in the burst is masked;
plain Write with DM disabled must drive DMI low. Masked Write supports only
BL16; if the device is configured for BL32, the controller supplies only 16
bits of data for the masked write. Back-to-back masked writes to the same bank
must be separated by tCCDMW = 32 tCK.

DBI limits the number of ones on the bus to cut power and improve DC balance.
The DRAM decides read inversion per byte based on the bit count; the controller
decides write inversion.

## What LPDDR4 does not have

- No dedicated DM pin (the function moved to DMI).
- No parity on the CA bus.
- No write CRC; data integrity relies on DBI plus system-level schemes.
- No on-die ECC.
- No DLL, no burst chop, no interleaved burst order, no additive latency.

**Source:** JESD209-4E section 3, 3.4.1 (MR1, MR2, MR3, MR13), 4.4, 4.5,
4.6, 4.8, 4.9, 4.10, 4.12, 4.13, 4.14, 4.15, 4.16, Table 95, Table 100
