# Refresh and Self-Refresh Timing

## Refresh parameters

DRAM cells leak; every row must be refreshed within the retention window.
Refresh is all-banks and internally addressed - the controller only
schedules it.

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tREFI | Average interval between refresh commands | REF -> REF (average) | 7.8 us at 0-85 C case; 3.9 us at 85-95 C (optional extended range) |
| tRFC | Refresh cycle time: refresh in progress, no other command | REF -> ACT, REF -> REF | 75 ns (256 Mb), 105 (512 Mb), 127.5 (1 Gb), 195 (2 Gb), 327.5 (4 Gb) |

Rules:

- All banks must be precharged (and tRP met) before REF.
- Up to 8 refresh commands may be postponed (posted), so the worst-case
  gap between two REFs is 9 x tREFI. Posting buys scheduling freedom to
  finish a burst sequence or a tFAW window first; it is not free - the
  postponed REFs land as a cluster later.
- Violating refresh timing silently corrupts data; the spec says the data
  must be rewritten before any valid read.
- tRFC grows steeply with density because one REF must touch more array.
  At 4 Gb, refresh duty cycle = tRFC/tREFI is ~4% of all bus time.

## Self-refresh

The DRAM refreshes itself with the external clock stopped: for sleep
states where the controller is powered down but memory contents must
survive.

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tCKE | Minimum CKE pulse, high or low - sets the minimum self-refresh stay | SRE -> SRX (and any CKE pulse) | 3 clocks |
| tXSNR | Exit self-refresh to any non-read command | SRX (CKE high) -> e.g. ACT, PRE, MRS | tRFC + 10 ns |
| tXSRD | Exit self-refresh to a read command | SRX -> RD | 200 clocks |

Entry checklist: all banks idle, ODT off (low), then REF encoding with
CKE falling. The DLL shuts down automatically.

Exit checklist: stable clock first, then CKE high; NOP/DES through the
exit window; wait tXSNR for non-read commands or tXSRD for reads (the DLL
is re-locking - same 200-clock rule as init); issue at least one REF
before re-entering self-refresh (an internally timed refresh may have
been skipped at the exit boundary); keep ODT off until tXSRD is met.

PASR (EMR2 A2-A0) limits self-refresh to a fraction of the array (full,
half, quarter, 1/8, 3/4 - the bank mapping depends on the code and bank
count). Anything outside the refreshed region is gone on entry. The
high-temperature bit (EMR2 A7) doubles the internal refresh rate above
85 C where leakage doubles.

## Power-down exit timings (related CKE rules)

| Symbol | Definition | Value |
| --- | --- | --- |
| tXP | Precharge power-down exit to any command | 2 clocks |
| tXARD | Active power-down exit (fast mode, DLL on) to read | 2 clocks |
| tXARDS | Active power-down exit (slow mode, DLL off) to read | 6 - AL clocks (7 - AL at 667, 8 - AL at 800) |
| tANPD / tAXPD | ODT low before PD entry / ODT valid after PD exit | 3 / 8 clocks |

Fast vs slow exit is an MR (A12) choice per system: fast keeps the DLL
burning through active power-down for a 2-clock resume; slow saves that
power but pays the longer exit.

**Source:** JESD79-2F sections 3.9, 3.10, 3.11, Table 40, Tables 42-43
