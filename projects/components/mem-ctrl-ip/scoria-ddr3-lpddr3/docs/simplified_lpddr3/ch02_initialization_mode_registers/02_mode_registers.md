# Mode Registers

LPDDR3 replaces the MRS/EMRS encoding of desktop DDR with two dedicated commands: MRW (write) and MRR (read). Both carry an 8-bit register address (MA0-MA7) on the CA bus, and each register is 8 bits wide (OP0-OP7). MRW is allowed only when all banks are idle; MRR may be issued from the all-banks-idle or banks-active state.

## Register map (SDRAM view)

| MR | Name | Access | Contents |
| --- | --- | --- | --- |
| MR0 | Device Info | R | DAI, RZQI, WL Set B support, RL3 option support |
| MR1 | Device Feature 1 | W | BL, nWR |
| MR2 | Device Feature 2 | W | RL/WL, nWRE, WL set select, WR leveling enable |
| MR3 | I/O Config 1 | W | DS (drive strength) |
| MR4 | Refresh Rate | R | Temperature-compensated refresh multiplier, TUF |
| MR5 | Basic Config 1 | R | Manufacturer ID |
| MR6 | Basic Config 2 | R | Revision ID1 |
| MR7 | Basic Config 3 | R | Revision ID2 |
| MR8 | Basic Config 4 | R | I/O width, density, type |
| MR9 | Test Mode | W | Vendor-specific test mode |
| MR10 | IO Calibration | W | ZQ calibration codes |
| MR11 | ODT Control | W | DQ ODT value, power-down ODT behavior |
| MR16 | PASR Bank Mask | W | Per-bank self-refresh mask |
| MR17 | PASR Segment Mask | W | Per-segment self-refresh mask |
| MR32 | DQ Calibration Pattern A | R | Read-only training pattern |
| MR40 | DQ Calibration Pattern B | R | Read-only training pattern |
| MR41 | CA Training 1 | W | Enter CA training |
| MR42 | CA Training 2 | W | Exit CA training |
| MR48 | CA Training 3 | W | Switch CA-to-DQ mapping during CA training |
| MR63 | Reset | W | Any write triggers MRW RESET |

Rules: RFU bits are written 0 and read as 0; reserved registers must not be written; writes to read-only registers have no effect.

## Programming rules

- MRW can only be issued when all banks are idle.
- The MRW command period is tMRW = 10 tCK; only NOP is allowed during tMRW.
- The delay from MRW registration to the next valid non-MRW command is tMRD = max(14 ns, 10 nCK).
- The MRR command period is tMRR = 4 tCK; only NOP is allowed during tMRR.
- MRR data is valid only on DQ[7:0] on the first beat; the remaining beats are undefined.
- Minimum MRR-to-MRW latency = RL + RU(tDQSCKmax/tCK) + BL/2 + 1 clock cycles.
- Minimum MRR-to-write latency = RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL clock cycles.

## MR0 - Device Information

| Field | Bits | Meaning |
| --- | --- | --- |
| DAI | OP0 | 0 = auto-initialization complete; 1 = still in progress |
| RZQI | OP4:3 | ZQ-pin self-test result (optional) |
| WL Set B support | OP6 | 1 = device supports WL Set B |
| RL3 option support | OP7 | 1 = device supports RL=3/nWR=3/WL=1 at <= 166 MHz |

## MR1 - Device Feature 1

| Field | Bits | Encodings |
| --- | --- | --- |
| BL | OP2:0 | 011 = BL8 (default); all others reserved |
| nWR (nWRE=0) | OP7:5 | 001=3 (optional), 100=6, 110=8, 111=9 |
| nWR (nWRE=1) | OP7:5 | 000=10 (default), 001=11, 010=12, 100=14, 110=16 |

Program nWR to RU(tWR/tCK); it sets when the internal precharge starts for a write with auto-precharge.

## MR2 - RL and WL

| OP3:0 | Set A (OP6=0) | Set B (OP6=1) |
| --- | --- | --- |
| 0001 | RL=3 / WL=1 | RL=3 / WL=1 |
| 0100 | RL=6 / WL=3 | RL=6 / WL=3 |
| 0110 | RL=8 / WL=4 | RL=8 / WL=4 |
| 0111 | RL=9 / WL=5 | RL=9 / WL=5 |
| 1000 | RL=10 / WL=6 (default) | RL=10 / WL=8 |
| 1001 | RL=11 / WL=6 | RL=11 / WL=9 |
| 1010 | RL=12 / WL=6 | RL=12 / WL=9 |
| 1100 | RL=14 / WL=8 | RL=14 / WL=11 |
| 1110 | RL=16 / WL=8 | RL=16 / WL=13 |

OP4 (nWRE) selects the nWR range; OP6 selects WL Set A or B; OP7 enables write leveling.

## MR3 - Drive Strength

| OP3:0 | Nominal impedance |
| --- | --- |
| 0001 | 34.3 ohm pull-down / pull-up |
| 0010 | 40 ohm pull-down / pull-up (default) |
| 0011 | 48 ohm pull-down / pull-up |
| 0100 | reserved for 60 ohm |
| 0110 | reserved for 80 ohm |
| 1001 | 34.3 ohm pull-down / 40 ohm pull-up |
| 1010 | 40 ohm pull-down / 48 ohm pull-up |
| 1011 | 34.3 ohm pull-down / 48 ohm pull-up |

## MR4 - Refresh Rate and Temperature

- OP2:0 reports the refresh multiplier (RM) recommended for the current temperature: 4x, 2x, 1x (<= 85 C), 0.5x, 0.25x without AC de-rating, or 0.25x with AC de-rating. Codes 000 and 111 mean the temperature operating limit is exceeded.
- OP7 (TUF) is set when OP2:0 has changed since the last MR4 read; reading MR4 clears TUF.
- When the de-rating code is selected, add 1.875 ns to tRCD, tRC, tRAS, tRP and tRRD, and apply the tDQSCK de-rating from the AC table.

## MR10 - ZQ Calibration Codes

| Code | Command | Latency |
| --- | --- | --- |
| 0xFF | Initialization calibration | tZQINIT = 1 us |
| 0xAB | Long calibration | tZQCL = 360 ns |
| 0x56 | Short calibration | tZQCS = 90 ns |
| 0xC3 | ZQ reset (default calibration) | tZQRESET = 50 ns |

If ZQ is tied to VDDCA, the device uses default calibration and ignores ZQ commands.

## MR11 - ODT Control

| Field | Bits | Encodings |
| --- | --- | --- |
| DQ ODT | OP1:0 | 00 = disable (default), 01 = RZQ/4, 10 = RZQ/2, 11 = RZQ/1 |
| PD Control | OP2 | 0 = ODT disabled during power-down (default), 1 = ODT enabled during power-down |

RZQ/4 is required for LPDDR3-1866 and -2133 and optional for lower speed grades.

## MR16 / MR17 - PASR Masks

- MR16 OP7:0 is a per-bank mask for 8-bank devices; a 1 blocks refresh to that bank.
- MR17 OP7:0 is a per-segment mask; a 1 blocks refresh to that segment of row space in every bank.

Masked regions lose data in self-refresh.

## MR32 / MR40 - DQ Calibration Patterns

MRR to MR32 returns Pattern A; MRR to MR40 returns Pattern B. These read-only patterns are used for DQ calibration.

## MR41 / MR42 / MR48 - CA Training

- MR41 enters CA training.
- MR48 changes the CA-to-DQ mapping so the remaining CA pins (CA4, CA9) can be calibrated.
- MR42 exits CA training.

MR41 and MR42 use special encodings whose rising-edge and falling-edge values are identical, so the device recognizes them even before CA timing has been adjusted.

## MR63 - Reset

Any MRW to MR63 performs a device reset. The operand 0xFC is recommended before CA training because it keeps the CA bus stable across the rising and falling clock edges.

**Source:** JESD209-3C sections 3.4.1, 4.10, 4.11, 4.11.2, 4.11.3
