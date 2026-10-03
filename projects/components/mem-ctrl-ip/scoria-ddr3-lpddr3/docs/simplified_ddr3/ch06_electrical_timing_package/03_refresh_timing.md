# Refresh and Self-Refresh Timing

## Refresh parameters

DRAM cells leak; every row must be refreshed within the retention window.
Refresh is all-banks and internally addressed - the controller only
schedules it. DDR3 has no per-bank refresh command.

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tREFI | Average interval between refresh commands | REF -> REF (average) | 7.8 us at case 0-85 C; 3.9 us at 85-95 C (extended-temperature parts) |
| tRFC | Refresh cycle time: refresh in progress, no other command | REF -> ACT, REF -> REF | 90 ns (512 Mb), 110 (1 Gb), 160 (2 Gb), 260 (4 Gb), 350 (8 Gb) |

Rules:

- All banks must be precharged (and tRP met) before REF.
- Up to 8 refresh commands may be postponed, so the maximum interval
  between two surrounding REFs is 9 x tREFI.
- Up to 8 may be pulled in; at most 16 REFs may fall in any 2 x tREFI
  window.
- Violating refresh timing silently corrupts data; the spec requires
  that data be rewritten before any valid read.
- tRFC grows steeply with density because one REF must touch more array.
  At 8 Gb, refresh duty cycle = tRFC/tREFI is about 4.5% of all bus time.

## Self-refresh

The DRAM refreshes itself with the external clock ignored: for sleep
states where the controller is powered down but memory contents must
survive. DDR3 renames the exit parameters (tXS/tXSDLL where DDR2 said
tXSNR/tXSRD).

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tCKE | Minimum CKE pulse width, high or low | any CKE pulse; SRE -> SRX floor | max(3 nCK, 7.5 ns at 800, 5 ns at 1600+) |
| tCKESR | Minimum CKE low width for self-refresh entry to exit | SRE -> SRX | tCKE(min) + 1 nCK |
| tXS | Exit self-refresh to commands not requiring a locked DLL | SRX (CKE high) -> ACT, PRE, MRS, REF | max(5 nCK, tRFC(min) + 10 ns) |
| tXSDLL | Exit self-refresh to commands requiring a locked DLL | SRX -> RD | tDLLK(min) = 512 nCK |
| tCKSRE | Valid clock required after self-refresh entry (and PD entry) | SRE -> clock may stop | max(5 nCK, 10 ns) of stable clock |
| tCKSRX | Valid clock required before self-refresh exit (and PD exit, reset exit) | stable clock -> SRX/PDX | max(5 nCK, 10 ns) |

Entry checklist: all banks idle, ODT off (low), REF encoding with CKE
falling. The DLL shuts down automatically.

Exit checklist: stable clock first (tCKSRX), then CKE high; NOP/DES
through the exit window; wait tXS for non-read commands or tXSDLL for
reads (the DLL is re-locking - same 512-clock rule as init); keep ODT off
until the exit window completes.

The refresh rate inside self-refresh is set by MR2: ASR (A6) auto-selects
from an internal temperature sensor where supported; SRT (A7) forces the
doubled 85-95 C rate. Above 85 C with SRT/ASR off, retention is not
guaranteed. If the part supports the extended temperature range at all,
normal-operation tREFI halves to 3.9 us.

## Power-down timings (related CKE rules)

| Symbol | Definition | Value |
| --- | --- | --- |
| tXP | Exit power-down (DLL on) to any valid command; also precharge-PD-with-frozen-DLL to non-DLL commands | max(3 nCK, 7.5 ns at 800/1066, 6 ns at 1333+) |
| tXPDLL | Exit precharge power-down with DLL frozen to DLL-requiring commands | max(10 nCK, 24 ns) |
| tCPDED | Command pass disable delay after PD entry | 1 nCK (2 at 1866/2133) |
| tPD | Power-down entry to exit timing | tCKE(min) to 9 x tREFI |
| tACTPDEN / tPRPDEN | ACT / PRE or PREA to PD entry | 1 nCK (2 at 1866/2133) |
| tRDPDEN | RD/RDA to PD entry | RL + 4 + 1 nCK |
| tWRPDEN | WR to PD entry (BL8/OTF/BC4OTF) | WL + 4 + RU(tWR/tCK) |
| tWRAPDEN | WRA to PD entry (BL8/OTF/BC4OTF) | WL + 4 + WR + 1 |
| tMRSPDEN | MRS to PD entry | tMOD(min) |

Fast vs slow exit is the MR0 A12 choice for precharge power-down: fast
exit keeps the DLL running for a tXP-class resume; slow exit freezes the
DLL and pays tXPDLL on the way out. Active power-down always uses fast
exit. Power-down performs no refresh: duration is bounded by the refresh
requirements, 9 x tREFI at best with 8 REFs posted beforehand. In
power-down with the DLL frozen, ODT turns asynchronous (tAONPD/tAOFPD,
2-8.5 ns).

**Source:** JESD79-3F sections 4.15-4.17, 12.2 (Table 61), 13.1 (Table 68)
