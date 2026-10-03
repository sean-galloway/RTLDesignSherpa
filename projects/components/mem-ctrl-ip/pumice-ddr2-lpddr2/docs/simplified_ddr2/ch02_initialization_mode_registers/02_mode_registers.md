# Mode Registers

Four registers, selected by bank address during an MRS/EMRS command:
MR (BA=00), EMR1 (BA=01), EMR2 (BA=10), EMR3 (BA=11). All must be
programmed at init; all writes require all banks idle and tMRD spacing.

## MR - Mode Register (BA1=0, BA0=0)

| Field | Bits | Meaning |
| --- | --- | --- |
| Burst length | A2-A0 | 010 = BL4, 011 = BL8 (only two legal values) |
| Burst type | A3 | 0 = sequential, 1 = interleaved |
| CAS latency | A6-A4 | CL 2-6 by encoding; no half-clock latencies in DDR2 |
| Test mode | A7 | Must be 0 for normal operation |
| DLL reset | A8 | 1 = issue DLL reset (self-clearing) |
| Write recovery | A11-A9 | WR in clocks: codes for 2, 3, 4, 5, 6 |
| PD exit mode | A12 | 0 = fast exit (tXARD), 1 = slow exit (tXARDS) |

WR is programmed in clocks, computed by rounding tWR[ns] / tCK up. It also
feeds tDAL (write auto-precharge recovery + precharge) as WR + tRP.

## EMR1 - Extended Mode Register 1 (BA1=0, BA0=1)

| Field | Bits | Meaning |
| --- | --- | --- |
| DLL enable | A0 | 0 = enable (required for normal operation) |
| Output drive | A1 | 0 = full strength, 1 = reduced strength |
| Rtt (ODT) | A6, A2 | 00 = off, 01 = 75 ohm, 10 = 150 ohm, 11 = 50 ohm |
| Additive latency | A5-A3 | AL = 0, 1, 2, 3, 4 (5 optional) |
| OCD program | A9-A7 | 000 exit, 001 drive(1), 010 drive(0), 100 adjust, 111 default |
| DQS disable | A10 | 1 = single-ended DQS mode (DQS# tied off externally) |
| RDQS enable | A11 | 1 = DM pin becomes RDQS (x8 parts; disables DM) |
| Qoff | A12 | 1 = output buffers disabled (IDD measurement aid) |

Notes: the 50 ohm Rtt option is mandatory at DDR2-800, optional below. If
RDQS is enabled, the write data mask function is lost on that pin. When
issuing later EMR1 writes for other reasons, A9-A7 must be 000 or the OCD
setting is disturbed.

## EMR2 - Extended Mode Register 2 (BA1=1, BA0=0)

Refresh-related features; everything else reserved-zero.

| Field | Bits | Meaning |
| --- | --- | --- |
| PASR | A2-A0 | Partial array self refresh: full, half, quarter, 1/8, 3/4 array (which banks depends on code; optional feature) |
| DCC | A3 | Duty Cycle Corrector enable (optional, may not be controllable) |
| SRF | A7 | High-temperature self-refresh rate enable (>85 C; optional) |

If PASR is set beyond full array, data outside the selected banks is lost
on self-refresh entry. If unsupported, PASR must be 000.

## EMR3 - Extended Mode Register 3 (BA1=1, BA0=1)

No function is defined. All address bits reserved-zero. It must still be
written during initialization.

## Programming rules

- Precondition: all banks precharged, CKE high.
- Every MRS/EMRS write redefines the whole register; always drive every
  field intentionally.
- tMRD = 2 clocks between any MRS/EMRS and the next command.
- Reserved bits and BA2/A13-A15: drive 0.

**Source:** JESD79-2F sections 3.4, 3.4.1, 3.4.2
