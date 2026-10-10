# Acronyms and Conventions

Terms used precisely in this book.

## Signal names

| Term | Meaning |
| --- | --- |
| CK_t / CK_c | Differential clock. Positive edge = CK_t rising through CK_c falling |
| CKE | Clock enable. SDR, sampled on the positive clock edge; gates all power states |
| CS_n | Chip select. SDR, sampled on the positive clock edge; contributes to the command code |
| CA0-CA9 | 10-bit DDR command/address bus; sampled on both clock edges |
| CA / CATR | Command/address bus / CA training mode entered via MR41/MR42/MR48 |
| CAxr / CAxf | CA bit x on the rising (r) / falling (f) edge of the clock |
| DQ | Bidirectional data |
| DQS_t / DQS_c | Differential data strobe, one pair per byte lane; edge-aligned on reads, center-aligned on writes |
| DM | Data mask, one per byte lane; masks write data when sampled high |
| ODT | Asynchronous on-die termination control pin for the DQ bus |
| ZQ | Pin used as reference for output drive-strength calibration |

## Commands

| Term | Meaning |
| --- | --- |
| ACT | Activate (open a row in a bank) |
| RD / WR | Burst read / burst write |
| PRE | Precharge (close a row); per-bank or all-bank via the AB flag |
| REFab / REFpb | Refresh, all banks / one per-bank-refresh bank |
| MRR / MRW | Mode register read / mode register write |
| NOP | No operation |
| SREF / PD / DPD | Self-refresh, power-down, deep power-down |

## Architecture terms

| Term | Meaning |
| --- | --- |
| Prefetch (8n) | Words moved internally per column access; LPDDR3 = 8n |
| BL | Burst length; fixed at 8 for LPDDR3 |
| RL / WL | Read latency / write latency, in clocks, programmed in MR0/MR2 |
| nWR | Write recovery in clocks for auto-precharge, programmed in MR1 |
| AP | Auto-precharge flag (CA0f of a RD/WR command) |
| AB | All-bank flag (CA4r of a PRE command) |
| RU{} | Round-up function; RU{x} = smallest integer >= x |
| CA training | Training mode to center CA inputs; entered/exited via MR41/MR42 |
| Write leveling | Training mode to align DQS with the clock; entered/exited via MRW |
| DQ calibration | MRR reads from MR32/MR40 return predefined calibration patterns |

## Power and refresh terms

| Term | Meaning |
| --- | --- |
| PASR | Partial array self-refresh: refresh only masked banks/segments in self-refresh |
| RM | Refresh multiplier from MR4; tREFIM = RM x tREFI |
| DAI | Device auto-initialization status bit (MR0 OP0) |
| TUF | Temperature update flag (MR4 OP7) |
| DPD | Deep power-down; array contents lost, full re-init required on exit |
| HSUL_12 | High-speed unterminated logic, 1.2 V: the LPDDR3 IO standard |
| tREFW / tREFI / tREFIM | Refresh window / average refresh interval / multiplied refresh interval |
| tRFCab / tRFCpb | Refresh cycle time, all-bank / per-bank |
| RZQ | 240 ohm reference resistor for output driver and ODT calibration |

## Conventions

- H/L in truth tables are logic high/low at the sampled edge; X is
  "don't care" but must still be a valid logic level.
- Timing symbols are written as plain text: tRCD, tWTR, tREFIpb.
- Anything the spec leaves unspecified is illegal; after an illegal
  event the part has to be reset through a full power-down/re-init cycle.

**Source:** JESD209-3C sections 2.4 (Table 2), 3.4.1, 4.8, 4.9.1, 4.12
