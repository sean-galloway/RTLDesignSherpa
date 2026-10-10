# Mode Registers

LPDDR2 replaces the MRS/EMRS command-address encoding of desktop DDR
with two dedicated commands: MRW (write) and MRR (read), each carrying
an 8-bit register address (MA0-MA7) on the CA bus. Mode registers are
8 bits wide (OP0-OP7). The table below covers every register that
matters for SDRAM operation; the NVM-only registers (MR20-MR31) are
omitted.

## Register map (SDRAM view)

| MR | Name | Access | Contents |
| --- | --- | --- | --- |
| MR0 | Device Info | R | DAI (init done), DI (SDRAM vs NVM), DNVI, RZQI |
| MR1 | Device Feature 1 | W | BL, BT, WC, nWR |
| MR2 | Device Feature 2 | W | RL & WL |
| MR3 | I/O Config 1 | W | DS (drive strength) |
| MR4 | Refresh Rate / Temp | R | Refresh-rate code, TUF flag |
| MR5 | Basic Config 1 | R | Manufacturer ID |
| MR6 / MR7 | Basic Config 2/3 | R | Revision ID1 / ID2 |
| MR8 | Basic Config 4 | R | I/O width, density, type (S2/S4/N) |
| MR9 | Test Mode | W | Vendor-specific test mode |
| MR10 | IO Calibration | W | ZQ calibration codes |
| MR16 | PASR Bank Mask | W | Self-refresh bank masking (S2 ranges; S4 per-bank bits) |
| MR17 | PASR Segment Mask | W | Segment masking (1 Gb+ S4 only) |
| MR32 / MR40 | DQ Cal Pattern A/B | R | Read-only training patterns |
| MR63 | Reset | W | Any write = MRW Reset |

Rules: RFU bits are written 0 and read as 0; writes to read-only
registers have no effect; reserved registers must not be written.

## MR1 - Device Feature 1 (the one you always program)

| Field | Bits | Encodings |
| --- | --- | --- |
| BL | OP2-0 | 010 = BL4 (default), 011 = BL8, 100 = BL16 |
| BT | OP3 | 0 = sequential (default), 1 = interleaved |
| WC | OP4 | 0 = wrap (default), 1 = no-wrap (BL4 only) |
| nWR | OP7-5 | 001..110 = nWR 3..8 (default 3); RU(tWR/tCK) |

nWR tells the device when to start the internal precharge after a write
with auto-precharge (AP=1). Program it to RU(tWR/tCK).

## MR2 - RL & WL

| OP3-0 | RL / WL | | OP3-0 | RL / WL |
| --- | --- | --- | --- | --- |
| 0001 | 3 / 1 (default) | | 0100 | 6 / 3 |
| 0010 | 4 / 2 | | 0101 | 7 / 4 |
| 0011 | 5 / 2 | | 0110 | 8 / 4 |

Pick the pair whose RL supports the target frequency (see the speed
table in Chapter 6).

## MR3 - Drive strength (DS)

| OP3-0 | Pull-down (typ) |
| --- | --- |
| 0001 | 34.3 ohm |
| 0010 | 40 ohm (default) |
| 0011 | 48 ohm |
| 0100 | 60 ohm |
| 0110 | 80 ohm |
| 0111 | 120 ohm (optional) |

## MR4 - Refresh rate and temperature (read-only)

- OP2-0: the device's recommended refresh rate for the current
  temperature: 4x, 2x, 1x (<= 85 C), 0.25x (with or without AC
  de-rating), or a temperature-limit-exceeded code. This is the
  temperature-compensated self-refresh (TCSR) mechanism: the controller
  scales tREFI/tREFW by this factor.
- OP7 (TUF): set when OP2-0 changed since the last MR4 read; reading
  MR4 clears it.
- When OP2-0 requests de-rating, add 1.875 ns to tRCD, tRC, tRAS, tRP
  and tRRD (and de-rate tDQSCK per the AC table).

## MR10 - ZQ calibration codes

| Code | Command | Latency |
| --- | --- | --- |
| 0xFF | Initialization calibration (after power-up) | tZQINIT = 1 us |
| 0xAB | Long calibration | tZQCL = 360 ns |
| 0x56 | Short calibration | tZQCS = 90 ns |
| 0xC3 | ZQ reset (default calibration) | tZQRESET = 50 ns |

S2 devices ignore ZQ commands. If ZQ is tied to VDDCA the device runs
default calibration and ignores ZQ commands entirely.

## MR16 / MR17 - PASR masks

- S2: MR16 OP1-0 selects full / 1/2 / 1/4 / 1/8 array, always anchored
  at bank 0 (lower banks keep refresh).
- S4: MR16 OP7-0 is a per-bank mask; 1 blocks refresh to that bank.
- S4, 1 Gb and up: MR17 OP7-0 is a per-segment mask (8 segments, each
  an eighth of the row space of every bank); 1 blocks refresh to that
  segment.

Masked regions lose data in self-refresh. See Chapter 3 (self-refresh)
and Chapter 6 (refresh timing).

**Source:** JESD209-2F section 3.5 (Tables 17-22), 5.13.4
