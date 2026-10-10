# Refresh and Self-Refresh Timing

## Refresh parameters

LPDDR4 keeps the LPDDR refresh-window model and doubles the command
count: 8192 REFab per 32 ms window (versus LPDDR3's 4096), so the
average interval is 3.904 us, not 7.8.

| Symbol | Definition | Value |
| --- | --- | --- |
| tREFW | Refresh window (1x rate) | 32 ms; extensible at reduced refresh rates per MR4 OP[2:0] |
| R | Required REFab commands per window | 8192 (all densities) |
| tREFI | Average REFab interval | 3.904 us |
| tREFIpb | Average REFpb interval (per bank) | 488 ns |
| tRFCab | All-bank refresh cycle | 130 ns (1-2 Gb/ch), 180 (3-4), 280 (6-8), 380 (12-16) |
| tRFCpb | Per-bank refresh cycle | 60 ns (1-2), 90 (3-4), 140 (6-8), 190 (12-16) |
| tpbR2pbR | REFpb(bank x) -> REFpb(bank y) | 60 ns (1-4 Gb/ch), 90 (6 Gb/ch and up) |

Rules:

- Each channel refreshes independently - a dual-channel die runs two
  independent refresh schedules (and the power delivery must tolerate
  both firing together).
- REFpb walks banks round-robin through an internal counter; the target
  bank is busy tRFCpb while the other seven keep working, and tRFCpb
  must be met before an ACT or another REFpb hits the same bank and
  before any REFab.
- The refresh rate (1x/0.5x/0.25x-style multipliers) is selected by
  MR4 OP[2:0]; higher-than-1x rates shrink tRAS's maximum and stretch
  tREFW. Above 85 C the rate must double (tREFI 1.95 us class).
- Refresh Management (RFM, sec 4.47) adds a second obligation: an
  internal rolling accumulated-ACT counter (per bank) must be decremented
  with RFM commands before it saturates - activate-heavy traffic now
  has a refresh-like tax independent of tREFI.

## Self-refresh

| Symbol | Definition | Value |
| --- | --- | --- |
| tSR | Minimum self-refresh time | max(15 ns, 3 nCK) |
| tXSR | Exit self-refresh to next valid command | max(tRFCab + 7.5 ns, 2 nCK) |
| tXSR_abort | Fast-exit abort path (high-density parts) | tRFCpb + 17.5 ns |

Entry: all banks precharged, SRE encoding, clock may stop after the
entry window. Exit: stable clock, CKE high, wait tXSR (or take the
abort path on parts that offer it and re-issue the lost refresh). PASR
(via MR) still restricts refresh to a fraction of the array at the cost
of the rest.

## Power-down

| Symbol | Definition | Value |
| --- | --- | --- |
| tXP | Exit power-down to any valid command | max(7.5 ns, 5 nCK) |

Active and precharge power-down both exist; the array must still meet
its refresh schedule across the stay. Deep power-down is gone from the
user-visible command set compared with LPDDR3 - the modern mobile power
story is FSP clock/frequency switching plus power-down, not a
data-losing DPD state.

**Source:** JESD209-4E sections 4.19, 4.20, 4.21, 4.44, 4.47
