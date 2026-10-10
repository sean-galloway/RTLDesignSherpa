# Mode Registers

LPDDR4 uses MRW (write) and MRR (read) commands. Both carry an 8-bit register address (MA0-MA7) and an 8-bit operand (OP0-OP7). MRW requires all banks idle; MRR is allowed from all-banks-idle or banks-active states. RFU bits are written 0 and read as 0.

## Register map

| MR | Name | Access | Highlights |
| --- | --- | --- | --- |
| MR0 | Device Info | R | Refresh mode, latency mode, RFM support, ZQ pin self-test, CA terminating rank, scaling support |
| MR1 | Device Feature 1 | W | BL, nWR, read/write preamble, post-amble |
| MR2 | RL / WL | W | RL, WL, WL set select, write-leveling enable |
| MR3 | I/O Config | W | DBI-WR/RD, PDDS, PPR protect, write post-amble, PU-CAL |
| MR4 | Refresh / Temp | R/W | Refresh rate, TUF, SR abort, PPR entry, thermal offset |
| MR5-MR7 | IDs | R | Manufacturer and revision IDs |
| MR8 | Basic Config | R | Type (S16, 16n prefetch), density, IO width |
| MR10 | ZQ Reset | W | OP[0]=1 resets calibration to defaults |
| MR11 | ODT Control | W | DQ ODT (OP[2:0]), CA ODT (OP[6:4]) |
| MR12 | VREF(CA) | R/W | Range and value for CA Vref |
| MR13 | FSP / Training | W | FSP-OP/WR, DMD, RRO, VRCG, VRO, RPT, CBT |
| MR14 | VREF(DQ) | R/W | Range and value for DQ Vref |
| MR16 | PASR Bank Mask | W | Per-bank self-refresh mask |
| MR17 | PASR Segment Mask | W | Per-row-segment self-refresh mask |
| MR18-MR19 | DQS Oscillator | R | Counter result from MPC Start DQS Osc |
| MR22 | ODT Details | W | SoC ODT, ODTE-CK/CS, ODTD-CA, byte-mode disable |
| MR23 | DQS Timer | W | Auto-stop interval for DQS oscillator |
| MR24 | RFM | R | RFM required, RAAIMT, RAAMMT |
| MR25 | PPR Resource | R | Per-bank PPR resource availability |
| MR26 | Scaling Level | R | Vendor scaling level (valid if MR0 OP[6]=1) |
| MR32 / MR40 | DQ Cal Patterns | W | Patterns returned by MPC Read DQ Calibration |

Many parameters above exist in two physical copies, one per Frequency Set Point. MR13 OP[6] (FSP-WR) selects which copy is accessed by MRW/MRR; MR13 OP[7] (FSP-OP) selects which copy drives current operation.

## Programming rules

| Symbol | Definition | Min |
| --- | --- | --- |
| tMRR | Gap occupied by an MRR (only DES allowed inside) | 8 tCK |
| tMRW | Gap occupied by an MRW (only DES allowed inside) | max(10 ns, 10 tCK) |
| tMRD | Wait from MRW registration to next non-MRW command | max(14 ns, 10 tCK) |
| tMRRI | Extra wait after power-down exit before MRR | tRCD + 3 tCK |
| tMPCWR | Extra wait after power-down exit before MPC Write FIFO | tRCD + 3 tCK |

MPC read/write training commands are followed immediately by a CAS-2 command whose operands are driven LOW. MPC ZQCal Start/Latch, DQS oscillator start/stop and NOP do not need CAS-2.

## MR0 - Device information

| Field | Bits | Meaning |
| --- | --- | --- |
| Refresh mode | OP[0] | 0 = legacy and modified refresh; 1 = modified refresh only |
| Latency mode | OP[1] | 0 = x16 latency; 1 = byte-mode latency |
| RFM support | OP[2] | 0 = TRR supported; 1 = RFM supported |
| RZQI | OP[4:3] | ZQ-pin self-test result (read after ZQ calibration) |
| SCLS | OP[6] | 1 = scaling level supported |
| CATR | OP[7] | 1 = this rank terminates CA (vendor specific) |

## MR1 - Burst and write recovery

| Field | Bits | Encodings |
| --- | --- | --- |
| BL | OP[1:0] | 00 = BL16; 01 = BL32; 10 = BL16/32 on-the-fly |
| WR-PRE | OP[2] | 0 = reserved; 1 = 2 tCK write preamble |
| RD-PRE | OP[3] | 0 = static; 1 = toggling read preamble |
| nWR | OP[6:4] | Programmed write-recovery for auto-precharge (encoding depends on MR26 scaling) |
| RPST | OP[7] | 0 = 0.5 tCK read post-amble; 1 = 1.5 tCK |

## MR2 - Read and write latency

| OP[2:0] | RL (x16, DBI-RD off) | WL (Set A / Set B) |
| --- | --- | --- |
| 000 | 6 (default) | 4 / 4 |
| 001 | 10 | 6 / 8 |
| 010 | 14 | 8 / 12 |
| 011 | 20 | 10 / 18 |
| 100 | 24 | 12 / 22 |
| 101 | 28 | 14 / 26 |
| 110 | 32 | 16 / 30 |
| 111 | 36 | 18 / 34 |

OP[6] selects WL Set A (0) or B (1). OP[7] enables write leveling. DBI-RD on in MR3 adds latency to RL (see spec tables).

## MR3 / MR11 - I/O and ODT

MR3: PDDS sets pull-down drive strength and Rx termination (RZQ/1 through RZQ/6). DBI-WR and DBI-RD enable data-bus inversion. PU-CAL selects VDDQ/2.5 or VDDQ/3 output-high calibration point.

MR11: DQ ODT (OP[2:0]) and CA ODT (OP[6:4]) each choose disable or RZQ/n.

## MR4 / MR13 / MR24 - Refresh, temperature, FSP and RFM

MR4 OP[2:0] reports the temperature-compensated refresh multiplier (4x down to 0.25x with/without de-rating). OP[7] (TUF) is set when the refresh code has changed since the last MRR to MR4. OP[4] enters PPR mode; OP[3] enables self-refresh abort.

MR13 OP[7:6] are FSP-OP and FSP-WR. OP[5] disables data masking when set. OP[4] enables additional refresh-rate codes. OP[3] speeds VREF settling; OP[0] enters command-bus training.

MR24 reports whether RFM is required (OP[0]), the initial RAA threshold (OP[5:1]) and the maximum RAA multiplier (OP[7:6]).

## MR12 / MR14 - Vref settings

MR12 controls VREF(CA); MR14 controls VREF(DQ). Each has a range bit (OP[6]) and a 6-bit value (OP[5:0]). Range[0] spans roughly 10%-30% of VDD2/VDDQ; Range[1] spans roughly 22%-42%.

## MR16 / MR17 / MR22 / MR25

- MR16 OP[7:0] masks individual banks from self-refresh.
- MR17 OP[7:0] masks row segments from self-refresh.
- MR22 fine-tunes command-bus termination: SoC ODT value, CK/CS ODT override for non-terminating ranks, and per-byte CA/CK/CS ODT disable in byte mode.
- MR25 OP[7:0] reads back per-bank PPR resource availability.

## MR32 / MR40 - DQ calibration patterns

MPC Read DQ Calibration returns MR32 (default 0x5A) followed by MR40 (default 0x3C) on the DQ bus. MR15 and MR20 invert the pattern on selected lower/upper byte DQ pins.

**Source:** JESD209-4E sections 3.4.1, 4.23, 4.24, 4.29, 4.35, 4.38, 4.47, 4.48
