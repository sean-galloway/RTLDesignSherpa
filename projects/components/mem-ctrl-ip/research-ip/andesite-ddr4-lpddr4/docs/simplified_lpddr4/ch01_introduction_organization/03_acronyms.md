# Acronyms and Conventions

Terms used precisely in this book.

## Signal names

| Term | Meaning |
| --- | --- |
| CK_t / CK_c | Differential clock. Positive edge = CK_t rising through CK_c falling |
| CKE | Clock enable. SDR, sampled on the positive clock edge; gates all power states |
| CS_n | Chip select. SDR, sampled on the positive clock edge; contributes to the command code |
| CA0-CA5 | 6-bit command/address bus; sampled on the rising clock edge |
| DQ | Bidirectional data |
| DQS_t / DQS_c | Differential data strobe, one pair per byte lane; edge-aligned on reads, center-aligned on writes |
| DMI | Data mask / data bus inversion pin, one per byte lane |
| ODT(ca) | On-die termination control for the CA bus |
| ODT | On-die termination for DQ/DQS/DMI |
| RESET_n | Active-low hardware reset pin |
| ZQ | Pin used as reference for output drive-strength and ODT calibration |

## Commands

| Term | Meaning |
| --- | --- |
| ACT | Activate (open a row in a bank) |
| RD / WR | Burst read / burst write |
| MWR | Masked write (write with byte-lane masking) |
| PRE | Precharge (close a row); per-bank or all-bank via the AB flag |
| REFab / REFpb | Refresh, all banks / one per-bank-refresh bank |
| RFM | Refresh management command |
| MRR / MRW | Mode register read / mode register write |
| MPC | Multi-purpose command (training, FIFO, ZQ, oscillator) |
| NOP | No operation |
| SREF / PD / DPD | Self-refresh, power-down, deep power-down |

## Architecture terms

| Term | Meaning |
| --- | --- |
| Prefetch (16n) | Words moved internally per column access; LPDDR4 = 16n |
| BL | Burst length; BL16 default, BL32 and on-the-fly optional |
| RL / WL | Read latency / write latency, in clocks, programmed in MR1/MR2 |
| nWR | Write recovery in clocks for auto-precharge, programmed in MR1 |
| nRTP | Read-to-precharge delay in clocks for auto-precharge |
| AP | Auto-precharge flag |
| AB | All-bank flag |
| RU{} | Round-up function; RU{x} = smallest integer >= x |
| RD{} | Round-down function; RD{x} = largest integer <= x |
| FSP | Frequency set point; two complete register sets for fast DVFS switching |
| FSP-OP | Selects which frequency set point is currently active |
| FSP-WR | Selects which frequency set point is accessed by MRW/MRR |
| DBIdc | Data bus inversion for power saving and signal integrity |
| WDQS | DQS control mode for write and masked write stability |
| PPR | Post-package repair of a failed row |

## Training and calibration terms

| Term | Meaning |
| --- | --- |
| CA training / CBT | Command bus training; aligns CA/CS with CK and sets VREF(CA) |
| VREF(CA) | Internal reference voltage for CA inputs, trained via MR12 |
| VREF(DQ) | Internal reference voltage for DQ inputs, trained via MR14 |
| VRCG | VREF current generator, enabled for faster VREF settling |
| Write leveling | Training mode to align DQS with the clock; entered/exited via MRW |
| DQ calibration | MPC reads return predefined calibration patterns from FIFOs |
| ZQCal | Output driver and termination calibration using the ZQ pin |

## Power and refresh terms

| Term | Meaning |
| --- | --- |
| PASR | Partial array self-refresh: refresh only masked banks/segments in self-refresh |
| Refresh Rate | TCSR refresh multiplier from MR4 |
| DAI | Device auto-initialization status bit (MR0 OP0) |
| TUF | Temperature update flag (MR4 OP7) |
| DPD | Deep power-down; array contents lost, full re-init required on exit |
| tREFW / tREFI / tREFIM | Refresh window / average refresh interval / multiplied refresh interval |
| tRFCab / tRFCpb | Refresh cycle time, all-bank / per-bank |
| RZQ | 240 ohm reference resistor for output driver and ODT calibration |

## Conventions

- H/L in truth tables are logic high/low at the sampled edge; X is "don't care"
  but must still be a valid logic level.
- Timing symbols are written as plain text: tRCD, tWTR, tREFIpb.
- tRTW is the book symbol for the read-to-write turnaround rule. The spec names
  the rule tRTW in the MPC timing table; the same symbol is used for the general
  RD->WR spacing in later timing tables.
- Anything the spec leaves unspecified is illegal; after an illegal event the
  part has to be reset through a full power-down/re-init cycle.

**Source:** JESD209-4E sections 2.4 (Tables 1-2), 3.4, 4.12, 4.16, 4.26-4.28, 4.35, 4.38, 4.47-4.48
