# Core Timing Parameters

The bank-state timings per channel (each LPDDR4 channel schedules
independently). Values are from the core AC timing table; convert ns to
clocks with RU(t/tCK).

## Row-cycle parameters

Like LPDDR3, LPDDR4 carries separate per-bank and all-bank precharge
times, and tRC is built from whichever one the history used:

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRCD | Row-to-column delay | ACT(bank x) -> RD/WR(bank x) | max(18 ns, 4 nCK) |
| tRPpb | Precharge recovery, single bank | PRE(bank x) -> ACT(bank x) | max(18 ns, 4 nCK) |
| tRPab | Precharge recovery, all banks | PREA -> ACT(any) | max(21 ns, 4 nCK) |
| tRAS | Row-open window | ACT(bank x) -> PRE(bank x) | min max(42 ns, 3 nCK); max min(9 x tREFI x refresh rate, 70.2 us) |
| tRC | Full row cycle | ACT(bank x) -> ACT(bank x) | tRAS + tRPab, or tRAS + tRPpb |

tPPD (precharge-to-precharge, 4 tCK) keeps back-to-back PRE commands off
each other's heels; it does not apply to auto-precharges.

## Activate-rate parameters

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRRD | ACT to ACT, any two banks | ACT(bank x) -> ACT(bank y) | max(10 ns, 4 nCK) |
| tFAW | Four-activate rolling window | any 4 ACTs within a sliding window | 40 ns (30 ns at 4267 Mb/s) |

## Data-to-precharge parameters

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRTP | Internal analog read must finish before the row closes | last read data(bank x) -> PRE(bank x) | max(7.5 ns, 8 nCK) |
| tWR | Write recovery: last write data committed before precharge | last write data(bank x) -> PRE(bank x) | max(18 ns, 6 nCK) x16; max(20 ns, 6 nCK) x8 |

nRTP and nWR are the programmed clock equivalents (RU of the ns value);
they set the auto-precharge start points after RD/WR with AP, and nRTP
grows by 8 clocks for BL32 bursts.

Command-spacing formulas (same bank):

| Transition | Earliest spacing (clocks) |
| --- | --- |
| RD -> PRE | BL/2 + max(8, RU(tRTP/tCK)) - 8 |
| WR -> PRE | WL + 1 + BL/2 + RU(tWR/tCK) |
| RD/WRA with AP -> ACT | auto-precharge starts nRTP/nWR after the burst end; next ACT >= tRP (pb or ab) after it actually starts, and >= tRC |

## Why these numbers dominate

tRCD/tRP remain the row-miss penalty, with the per-bank/all-bank choice
now routine: a controller that tracks open rows per bank will precharge
one bank at a time and pay tRPpb almost always, keeping PREA for idle-
drain events. tRRD/tFAW bound activate rate; the refresh-rate multiplier
(MR4) shrinks both tRAS's maximum and the tREFI schedule together when
the die runs hot or the vendor supports extended 1x windows.

**Source:** JESD209-4E sections 4.3 (Tables 88-89), 4.12, 4.17-4.19
