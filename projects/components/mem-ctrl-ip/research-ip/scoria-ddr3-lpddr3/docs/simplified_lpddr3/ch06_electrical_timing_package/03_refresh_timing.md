# Refresh and Self-Refresh Timing

## Refresh parameters

LPDDR3 counts refresh the LPDDR way: a fixed number of REFRESH commands
per refresh window, at either all-bank or per-bank granularity.

| Symbol | Definition | Value |
| --- | --- | --- |
| tREFW | Refresh window: every row refreshed inside it | 32 ms (16 ms at 1/2-rate, 8 ms at 1/4-rate PASR settings) |
| R | Required REFab commands per window | 4096 (8192 at 8 Gb and above) |
| tREFI | Average interval, REFab | 7.8 us |
| tREFIpb | Average interval, REFpb (per bank) | 0.975 us at 1 Gb, 0.4875 us above (8 x tREFIpb covers all banks) |
| tRFCab | All-bank refresh cycle time | 130 ns (1-4 Gb), 210 ns (6-8 Gb) |
| tRFCpb | Per-bank refresh cycle time | 60 ns (1-4 Gb), 90 ns (6-8 Gb) |

Rules:

- All banks must be idle (and tRP met) before REFab; REFpb only needs its
  target bank idle, and the target walks banks round-robin via an
  internal counter.
- REFpb buys scheduling freedom: one bank restores while the others keep
  serving. Eight REFpb (one per bank) equals one REFab of coverage.
- tFAW counts REFpb as an activate-class command - a cluster of per-bank
  refreshes eats activate budget.
- The refresh rate is set through MR4 (full, 1/2, 1/4 rate; temperature
  derating flag), and the RM multiplier in the tRAS maximum is the same
  knob seen from the row-timing side.
- Violating the refresh window silently corrupts data.

At 8 Gb, REFab at 210 ns per 7.8 us is about 2.7% of bus time; per-bank
refresh cuts the all-bank stall to 60-90 ns per bank.

## Self-refresh

The DRAM refreshes itself with the external clock stopped: the mobile
sleep state. PASR (MR16 bank mask, MR17 segment mask) restricts refresh
to a fraction of the array; anything outside is lost on entry.

| Symbol | Definition | Value |
| --- | --- | --- |
| tCKE | Minimum CKE pulse width, high or low | max(7.5 ns, 3 nCK) |
| tCKESR | Minimum CKE low width for self-refresh entry to exit | max(15 ns, 3 nCK) |
| tXSR | Exit self-refresh to next valid command | max(tRFCab + 10 ns, 2 nCK) |
| tCKSRE/tCKSRX | Valid clock required after entry / before exit | max(5 nCK, 10 ns) class (clock-stop rules) |

There is no separate DLL-relock wait as in DDR3: LPDDR3 has no DLL. Exit
needs a stable clock, CKE high, then tXSR. The temperature sensor (MR4)
doubles the internal refresh rate when the die runs hot.

## Power-down and deep power-down

| Symbol | Definition | Value |
| --- | --- | --- |
| tXP | Exit power-down to any valid command | max(7.5 ns, 3 nCK) |
| tMRRI | After tXP, extra wait before an MRR | tRCD(min) |
| tCPDED | Command pass disable delay after PD entry | 2 tCK |
| tDPD | Minimum deep power-down time | 500 us |

Power-down keeps the array alive (refresh obligations continue: 9 x
tREFI of slack at best); deep power-down does not - DPD drops the array
contents and every ODT/input for minimum power, and exit is a complete
re-initialization. ODT timing around the power states: disabled within
12 ns of PD entry, 12 + 0.5 tCK of SR/DPD entry, and re-enabled within
12 ns of exit. Clock stop is legal in idle and power-down, which is the
other big LPDDR3 power knob alongside DPD.

**Source:** JESD209-3C sections 4.8, 4.9, 4.13, 4.14, 11.3 (Table 62), 11.4 (Table 64)
