# Mode Registers

DDR3 provides four mode registers, selected by the bank-address pins during an MRS command. Their values are undefined after power-up, so all four must be written during initialization. Reprogramming later is allowed whenever all banks are idle.

Register select encoding:

| BA2 | BA1 | BA0 | Register |
| --- | --- | --- | --- |
| 0 | 0 | 0 | MR0 |
| 0 | 0 | 1 | MR1 |
| 0 | 1 | 0 | MR2 |
| 0 | 1 | 1 | MR3 |

## MR0 (BA2=BA1=BA0=0)

| Field | Bits | Encoding |
| --- | --- | --- |
| Burst length | A1-A0 | 00 = fixed BL8, 01 = on-the-fly BC4/BL8 via A12/BC#, 10 = fixed BC4, 11 = reserved |
| Read burst type | A3 | 0 = sequential, 1 = interleaved |
| CAS latency | A6-A4, A2 | see CL table below |
| Test mode | A7 | 0 = normal; 1 = manufacturer test only |
| DLL reset | A8 | 1 = reset (self-clearing) |
| Write recovery | A11-A9 | see WR table below |
| Precharge power-down DLL control | A12 | 0 = slow exit (DLL off), 1 = fast exit (DLL on) |

CL encoding:

| A6 | A5 | A4 | A2 | CL |
| --- | --- | --- | --- | --- |
| 0 | 0 | 1 | 0 | 5 |
| 0 | 1 | 0 | 0 | 6 |
| 0 | 1 | 1 | 0 | 7 |
| 1 | 0 | 0 | 0 | 8 |
| 1 | 0 | 1 | 0 | 9 |
| 1 | 1 | 0 | 0 | 10 |
| 1 | 1 | 1 | 0 | 11 (optional at DDR3-1600) |
| 0 | 0 | 0 | 1 | 12 |
| 0 | 0 | 1 | 1 | 13 |
| 0 | 1 | 0 | 1 | 14 |

All other A6:A4:A2 combinations are reserved. DDR3 has no half-clock latencies. Overall read latency is RL = AL + CL.

WR encoding:

| A11 | A10 | A9 | WR (cycles) |
| --- | --- | --- | --- |
| 0 | 0 | 0 | 16 |
| 0 | 0 | 1 | 5 |
| 0 | 1 | 0 | 6 |
| 0 | 1 | 1 | 7 |
| 1 | 0 | 0 | 8 |
| 1 | 0 | 1 | 10 |
| 1 | 1 | 0 | 12 |
| 1 | 1 | 1 | 14 |

Program WR to the ceiling of tWR(ns) / tCK(ns). It is used with tRP to determine tDAL for auto-precharge writes.

## MR1 (BA2=0, BA1=0, BA0=1)

| Field | Bits | Encoding |
| --- | --- | --- |
| DLL enable | A0 | 0 = enabled (required for normal operation), 1 = disabled |
| Output driver impedance | A5, A1 | 00 = RZQ/6, 01 = RZQ/7, others reserved |
| RTT_NOM (ODT) | A9, A6, A2 | 000 = off, 001 = RZQ/4, 010 = RZQ/2, 011 = RZQ/6, 100 = RZQ/12, 101 = RZQ/8, others reserved |
| Additive latency | A4-A3 | 00 = 0, 01 = CL-1, 10 = CL-2, 11 = reserved |
| Write leveling | A7 | 0 = off, 1 = enabled |
| TDQS enable | A11 | 0 = off, 1 = enabled (x8 only; disables DM) |
| Output disable (Qoff) | A12 | 0 = outputs enabled, 1 = DQ/DQS/DQS# disabled |

The DLL is automatically turned off during self-refresh and re-enabled on exit. When the DLL is disabled, synchronous ODT and dynamic ODT are not supported; keep ODT low and set Rtt_WR to off.

## MR2 (BA2=0, BA1=1, BA0=0)

| Field | Bits | Encoding |
| --- | --- | --- |
| CAS write latency | A5-A3 | see CWL table below |
| Auto self-refresh | A6 | 0 = manual (use SRT), 1 = ASR enabled (optional) |
| Self-refresh temperature | A7 | 0 = normal range, 1 = extended range (optional) |
| Dynamic ODT (Rtt_WR) | A10-A9 | 00 = off, 01 = RZQ/4, 10 = RZQ/2, 11 = reserved |
| Partial array self-refresh | A2-A0 | optional; see PASR table below |

CWL encoding:

| A5 | A4 | A3 | CWL | tCK(avg) range |
| --- | --- | --- | --- | --- |
| 0 | 0 | 0 | 5 | >= 2.5 ns |
| 0 | 0 | 1 | 6 | 2.5 ns > tCK >= 1.875 ns |
| 0 | 1 | 0 | 7 | 1.875 ns > tCK >= 1.5 ns |
| 0 | 1 | 1 | 8 | 1.5 ns > tCK >= 1.25 ns |
| 1 | 0 | 0 | 9 | 1.25 ns > tCK >= 1.07 ns |
| 1 | 0 | 1 | 10 | 1.07 ns > tCK >= 0.935 ns |
| 1 | 1 | 0 | 11 | 0.935 ns > tCK >= 0.833 ns |
| 1 | 1 | 1 | 12 | 0.833 ns > tCK >= 0.75 ns |

Overall write latency is WL = AL + CWL.

PASR encoding (optional; data outside selected banks is lost on self-refresh entry):

| A2 | A1 | A0 | Array kept active |
| --- | --- | --- | --- |
| 0 | 0 | 0 | Full array |
| 0 | 0 | 1 | Half array (BA 000-011) |
| 0 | 1 | 0 | Quarter array (BA 000-001) |
| 0 | 1 | 1 | 1/8 array (BA 000) |
| 1 | 0 | 0 | 3/4 array (BA 010-111) |
| 1 | 0 | 1 | Half array (BA 100-111) |
| 1 | 1 | 0 | Quarter array (BA 110-111) |
| 1 | 1 | 1 | 1/8 array (BA 111) |

## MR3 (BA2=0, BA1=1, BA0=1)

| Field | Bits | Encoding |
| --- | --- | --- |
| MPR operation | A2 | 0 = normal DRAM array, 1 = reads redirected to MPR |
| MPR location | A1-A0 | 00 = predefined pattern, 01-11 = reserved |

When A2 is 0, A1-A0 are ignored. With MPR enabled, only RD/RDA commands are legal until MPR is disabled.

## Programming rules

- Precondition: all banks precharged and idle, tRP satisfied, all bursts finished, CKE high.
- An MRS command rewrites the whole addressed register; always drive every field intentionally, including unchanged ones.
- Wait tMRD between consecutive MRS commands and tMOD before any non-MRS command (NOP/Deselect excluded).
- If RTT_NOM is enabled before or after the MRS, keep ODT low through the command and do not raise it until tMOD expires. If RTT_NOM is disabled, ODT may be either level.
- Drive BA2 and all reserved address bits to 0.
- MRS and DLL reset do not disturb stored array data.

**Source:** JESD79-3F sections 3.4.1, 3.4.2, 3.4.3, 3.4.4, 3.4.5
