# Acronyms and Conventions

Terms used precisely in this book.

## Signal names

| Term | Meaning |
| --- | --- |
| CK_t / CK_c | Differential clock. Positive edge = CK_t rising through CK_c falling |
| CKE | Clock enable. SDR, sampled on the positive clock edge; gates all power states |
| CS_n | Chip select. SDR, sampled on the positive clock edge; part of the command code |
| CA0-CA9 | 10-bit DDR command/address bus; sampled on both clock edges |
| CAxr / CAxf | CA bit x on the rising (r) / falling (f) edge of the clock |
| DQ | Bidirectional data |
| DQS_t / DQS_c | Differential data strobe, one pair per byte lane; edge-aligned on reads, center-aligned on writes |
| DM | Data mask, one per byte lane; masks write data when sampled high |
| ZQ | Reference pin for output drive-strength calibration |

## Commands

| Term | Meaning |
| --- | --- |
| ACT | Activate (open a row in a bank) |
| RD / WR | Burst read / burst write |
| PRE | Precharge (close a row); per-bank or all-bank via the AB flag |
| REFab / REFpb | Refresh, all banks / one per-bank-refresh bank |
| BST | Burst terminate |
| MRW / MRR | Mode register write / read |
| NOP | No operation (two legal encodings) |
| SREF / PD / DPD | Self-refresh, power-down, deep power-down |

## Architecture terms

| Term | Meaning |
| --- | --- |
| Prefetch (4n/2n) | Words moved internally per column access; S4 = 4n, S2 = 2n |
| BL / BT / WC | Burst length / burst type (sequential, interleaved) / wrap control (wrap, no-wrap) |
| RL / WL | Read latency / write latency, in clocks, programmed in MR2 |
| nWR | Write recovery in clocks for auto-precharge, programmed in MR1 |
| AP | Auto-precharge flag (CA0f of a RD/WR command) |
| AB | All-bank flag (CA4r of a PRE command) |
| RU{} | Round-up function; RU{x} = smallest integer >= x |

## Power and refresh terms

| Term | Meaning |
| --- | --- |
| PASR | Partial array self-refresh: refresh only masked banks/segments in self-refresh |
| TCSR | Temperature-compensated self refresh (refresh rate scaled by temperature, via MR4) |
| DAI | Device auto-initialization status bit (MR0 OP0) |
| TUF | Temperature update flag (MR4 OP7) |
| DNV | Data-not-valid (an NVM feature; SDRAM does not implement it) |
| HSUL_12 | High-speed unterminated logic, 1.2 V: the LPDDR2 IO standard |
| tREFW / tREFI | Refresh window / average refresh interval |
| tRFCab / tRFCpb | Refresh cycle time, all-bank / per-bank |

## Conventions

- H/L in truth tables are logic high/low at the sampled edge; X is
  "don't care (but a defined logic level)".
- Timing symbols are written as plain text: tRCD, tWTR, tREFIpb.
- Anything the spec leaves unspecified is illegal; after an illegal
  event the device must be powered down and re-initialized.

**Source:** JESD209-2F sections 2.12 (Table 2), 5.18 (notes to Table 60)
