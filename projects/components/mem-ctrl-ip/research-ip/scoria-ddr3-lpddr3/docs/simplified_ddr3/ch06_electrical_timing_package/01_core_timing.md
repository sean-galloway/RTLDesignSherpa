# Core Timing Parameters

The bank-state timings: what each parameter constrains, and the command
transition it applies to. Row-cycle values live in the speed-bin tables
(Tables 62-67, one per DDR3 grade); the ns figures below cite the range
across bins. Clock conversion: divide by tCK(avg) and round up (RU).

## Row-cycle parameters

| Symbol | Definition | Applies between | Min (typ bins) |
| --- | --- | --- | --- |
| tRCD | Row-to-column delay: the row must reach the sense amps before a column command executes | ACT(bank x) -> RD/WR(bank x) | 10-15 ns by bin (12.5 at DDR3-800D, 10 at DDR3-1600G) |
| tRP | Precharge recovery: sense amps and bitlines restored before re-activation | PRE(bank x) -> ACT(bank x) | 10-15 ns, bin-matched to tRCD |
| tRAS | Minimum row-open time: data must be restored to the cells before precharge | ACT(bank x) -> PRE(bank x) | 36-37.5 ns; max 9 x tREFI |
| tRC | Row cycle: full open-close-reopen loop for one bank | ACT(bank x) -> ACT(bank x) | 46.5-52.5 ns by bin |

Unlike DDR2 there is no extra clock for precharge-all: PREA and PRE both
use the same tRP in DDR3.

## Activate-rate parameters (cross-bank)

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRRD | Activate-to-activate spacing, any two banks (limits peak array current) | ACT(bank x) -> ACT(bank y) | max(4 nCK, X ns): 10 ns at DDR3-800, 7.5 at 1066, 6 at 1333/1600, 5 at 1866/2133 (1 KB pages; 2 KB pages 2.5 ns looser below 1333) |
| tFAW | Four-activate rolling window: at most 4 ACTs inside any window of this length | any 4 ACTs within a sliding window | 1 KB page: 40/37.5/30/30/27/25 ns at 800/1066/1333/1600/1866/2133; 2 KB page: 50/50/45/40/35/35 ns |

tFAW example with the drill model: if RU(tFAW/tCK) = 16 and an ACT lands
at clock N, at most three more ACTs may land in clocks N+1 .. N+15.

## Data-to-precharge parameters

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRTP | Read-to-precharge: internal analog read must finish before the row closes | internal RD(bank x) -> PRE(bank x) | max(4 nCK, 7.5 ns) |
| tWR | Write recovery: last write data must be committed to the cells before precharge | first CK after last write data(bank x) -> PRE(bank x) | 15 ns; programmed in clocks via MR0 (WR codes 5, 6, 7, 8, 10, 12, 14, 16) |
| tDAL | Write auto-precharge total: programmed WR plus precharge, before re-activation | WRA(bank x) -> ACT(bank x) | WR + RU(tRP/tCK(avg)) |

tRTP and tWR are referenced from the first rising CK edge after the last
data of the burst - not from the command. tWR grows slower than tCK
shrinks, so it costs more clocks at every new speed grade.

Command-spacing formulas that fall out of these (same bank):

| Transition | Earliest spacing (clocks) |
| --- | --- |
| RD -> PRE | AL + max(RU(tRTP), 4) - with tRTP's 4-nCK floor this is AL + RU(tRTP) |
| WR -> PRE | WL + BL/2 + RU(tWR) |
| RDA -> ACT | RU(tRP) after the auto-precharge actually starts (AL + BL/2 + RU(tRTP) after the RDA, delayed if tRAS is unmet), and >= tRC from the old ACT |
| WRA -> ACT | WL + BL/2 + WR + RU(tRP), and >= tRC |

## Why these four numbers dominate

tRCD and tRP are the row-miss penalty. tRAS + tRP = tRC bounds how fast
one bank can cycle rows. tRRD and tFAW bound how fast the whole device can
open rows regardless of how many banks are free - on activate-heavy
streams (many small transfers, open-page policy) tFAW is usually the
binding constraint, not tRRD. The controller's scheduler exists to hide
tRCD/tRP behind other banks' data and to pace ACTs against tRRD/tFAW.

**Source:** JESD79-3F sections 4.11-4.14, 12.3 (Tables 62-67), 13.1 (Table 68)
