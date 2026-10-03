# Mode Registers
DDR4 provides seven mode registers selected by the BG0, BA1, and BA0 pins during an MRS command. BG1 and A17 are reserved and must be driven to 0. Register values are undefined after power-up, so all seven must be written during initialization. Reprogramming later is allowed whenever all banks are idle.

Register select encoding:

| BG0 | BA1 | BA0 | Register |
| --- | --- | --- | --- |
| 0 | 0 | 0 | MR0 |
| 0 | 0 | 1 | MR1 |
| 0 | 1 | 0 | MR2 |
| 0 | 1 | 1 | MR3 |
| 1 | 0 | 0 | MR4 |
| 1 | 0 | 1 | MR5 |
| 1 | 1 | 0 | MR6 |
| 1 | 1 | 1 | RCW1 (ignored by DRAM) |

## MR0 (BG0=0, BA1=0, BA0=0)

| Field | Bits | Encoding |
| --- | --- | --- |
| Burst length | A1:A0 | 00 = fixed BL8, 01 = on-the-fly BC4/BL8 via A12, 10 = fixed BC4, 11 = reserved |
| Read burst type | A3 | 0 = sequential, 1 = interleaved |
| CAS latency | A12, A6:A4, A2 | see CL table |
| Test mode | A7 | 0 = normal, 1 = manufacturer test only |
| DLL reset | A8 | 1 = reset (self-clearing) |
| WR / RTP for auto-precharge | A13, A11:A9 | A[11:9] selects 10/12/14/16/18/20/24/22 cycles; A13=1 adds 26 cycles |

CL encoding:

| A12 | A6:A4 | A2 | CL |
| --- | --- | --- | --- |
| 0 | 000 | 0 | 9 |
| 0 | 000 | 1 | 10 |
| 0 | 001 | 0 | 11 |
| 0 | 001 | 1 | 12 |
| 0 | 010 | 0 | 13 |
| 0 | 010 | 1 | 14 |
| 0 | 011 | 0 | 15 |
| 0 | 011 | 1 | 16 |
| 0 | 100 | 0 | 18 |
| 0 | 100 | 1 | 20 |
| 0 | 101 | 0 | 22 |
| 0 | 101 | 1 | 24 |
| 0 | 110 | 0 | 23 |
| 0 | 110 | 1 | 17 |
| 0 | 111 | 0 | 19 |
| 0 | 111 | 1 | 21 |
| 1 | 000 | 0 | 25 |
| 1 | 000 | 1 | 26 |

Other combinations are reserved or device-specific. Overall read latency is RL = AL + CL. Program WR to a value equal to or greater than tWRmin in clock cycles; WR is used with tRP to determine tDAL for auto-precharge writes.
## MR1 (BG0=0, BA1=0, BA0=1)

| Field | Bits | Encoding |
| --- | --- | --- |
| DLL enable | A0 | 0 = disabled, 1 = enabled (opposite sense from DDR3) |
| Output driver impedance | A2:A1 | 00 = RZQ/7, 01 = RZQ/5, others reserved |
| RTT_NOM | A10:A8 | 000 = off, 001 = RZQ/4, 010 = RZQ/2, 011 = RZQ/6, 100 = RZQ/1, 101 = RZQ/5, 110 = RZQ/3, 111 = RZQ/7 |
| Additive latency | A4:A3 | 00 = 0, 01 = CL-1, 10 = CL-2, 11 = reserved |
| Write leveling enable | A7 | 0 = off, 1 = enabled |
| TDQS enable | A11 | 0 = off, 1 = enabled (x8 only; disables DM) |
| Output disable (Qoff) | A12 | 0 = outputs enabled, 1 = DQ/DQS/DQS# disabled |

When the DLL is disabled, synchronous ODT and dynamic ODT are not supported; keep ODT low and set Rtt_WR to off.
## MR2 (BG0=0, BA1=1, BA0=0)

| Field | Bits | Encoding |
| --- | --- | --- |
| CAS write latency | A5:A3 | 000 = 9, 001 = 10, 010 = 11, 011 = 12, 100 = 14, 101 = 16, 110 = 18, 111 = 20; final value also depends on read/write preamble |
| Low-power auto self-refresh | A7:A6 | 00 = manual normal temp, 01 = manual reduced temp, 10 = manual extended temp, 11 = ASR mode |
| Dynamic ODT (Rtt_WR) | A11:A9 | 000 = off, 001 = RZQ/2, 010 = RZQ/1, 011 = Hi-Z, 100 = RZQ/3, others reserved |
| Write CRC enable | A12 | 0 = disabled, 1 = enabled |

Overall write latency is WL = AL + CWL + PL, where PL is any programmed CA parity latency.
## MR3 (BG0=0, BA1=1, BA0=1)

| Field | Bits | Encoding |
| --- | --- | --- |
| MPR operation | A2 | 0 = normal DRAM array, 1 = reads/writes redirected to MPR |
| MPR page selection | A1:A0 | 00 = page 0, 01 = page 1, 10 = page 2, 11 = page 3 |
| Gear-down mode | A3 | 0 = 1N (1/2 rate), 1 = 2N (1/4 rate) |
| Per-DRAM addressability | A4 | 0 = disabled, 1 = enabled |
| Temperature sensor readout | A5 | 0 = disabled, 1 = enabled |
| Fine-granularity refresh | A8:A6 | 000 = fixed 1x, 001 = fixed 2x, 010 = fixed 4x, 101 = on-the-fly 2x, 110 = on-the-fly 4x, others reserved |
| Write CMD latency with CRC+DM | A10:A9 | 00 = 4 nCK, 01 = 5 nCK, 10 = 6 nCK, 11 = reserved |
| MPR read format | A12:A11 | 00 = serial, 01 = parallel, 10 = staggered, 11 = reserved |

With MPR enabled, only RD/RDA and MPR write commands are legal until MPR is disabled. Page 0 holds a training pattern, page 1 logs CA parity errors, page 2 reflects mode-register readouts and temperature status, and page 3 is vendor-specific.
## MR4 (BG0=1, BA1=0, BA0=0)

| Field | Bits | Encoding |
| --- | --- | --- |
| MBIST PPR | A0 | 0 = disabled, 1 = enabled |
| Maximum power saving mode | A1 | 0 = disabled, 1 = enabled |
| Temperature-controlled refresh range | A2 | 0 = normal, 1 = extended |
| Temperature-controlled refresh mode | A3 | 0 = disabled, 1 = enabled |
| Internal Vref monitor | A4 | 0 = disabled, 1 = enabled |
| Soft PPR | A5 | 0 = disabled, 1 = enabled |
| CS-to-CA latency (CAL) | A8:A6 | 000 = disable, 001 = 3, 010 = 4, 011 = 5, 100 = 6, 101 = 8, others reserved |
| Self-refresh abort | A9 | 0 = disabled, 1 = enabled |
| Read preamble training mode | A10 | 0 = disabled, 1 = enabled |
| Read preamble | A11 | 0 = 1 tCK, 1 = 2 tCK |
| Write preamble | A12 | 0 = 1 tCK, 1 = 2 tCK |
| Hard PPR | A13 | 0 = disabled, 1 = enabled |

## MR5 (BG0=1, BA1=0, BA0=1)

| Field | Bits | Encoding |
| --- | --- | --- |
| CA parity latency mode | A2:A0 | 000 = disabled, 001 = PL=4, 010 = PL=5, 011 = PL=6, others reserved |
| CRC error clear | A3 | 0 = clear, 1 = error |
| CA parity error status | A4 | 0 = clear, 1 = error |
| ODT input buffer in power-down | A5 | 0 = activated, 1 = deactivated |
| RTT_PARK | A8:A6 | same encoding as RTT_NOM |
| CA parity persistent error | A9 | 0 = disabled, 1 = enabled |
| Data mask (DM) | A10 | 0 = disabled, 1 = enabled |
| Write DBI | A11 | 0 = disabled, 1 = enabled |
| Read DBI | A12 | 0 = disabled, 1 = enabled |

When DM is enabled together with write CRC, an extra write-command latency is added as defined in MR3 A10:A9.
## MR6 (BG0=1, BA1=1, BA0=0)

| Field | Bits | Encoding |
| --- | --- | --- |
| VrefDQ training value | A5:A0 | valid training codes; step size is about 0.65 % per code |
| VrefDQ training range | A6 | 0 = range 1, 1 = range 2 |
| VrefDQ training enable | A7 | 0 = normal operation, 1 = training mode |
| tCCD_L and tDLLK | A12:A10 | 000 = 4/597, 001 = 5/597, 010 = 6/768, 011 = 7/768, 100 = 8/1024 nCK; 101-111 reserved |

The exact tCCD_L and tDLLK values depend on the operating data rate and the AC parameter tables.
## Programming rules
- Precondition: all banks precharged and idle, tRP satisfied, all bursts finished, CKE high.
- An MRS command rewrites the whole addressed register; always drive every field intentionally, including unchanged ones.
- Wait tMRD (8 nCK) between consecutive MRS commands and tMOD (max(24 nCK, 15 ns)) before any non-MRS command (NOP/Deselect excluded).
- If CA parity or CAL is enabled, use tMRD_PAR / tMOD_PAR or tMRD_CAL / tMOD_CAL instead of the plain values.
- If RTT_NOM is enabled before or after the MRS, keep ODT low through the command and do not raise it until tMOD expires. If RTT_NOM is disabled, ODT is a do not care during MRS.
- Drive BG1, A17, and all reserved address bits to 0.
- MRS and DLL reset do not disturb stored array data.

**Source:** JESD79-4D sections 3.4.1, 3.5, 4.7, 4.15, 4.17, 4.18
