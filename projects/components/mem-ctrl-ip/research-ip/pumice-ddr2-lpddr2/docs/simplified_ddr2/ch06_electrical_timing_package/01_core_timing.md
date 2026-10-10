# Core Timing Parameters

The bank-state timings: what each parameter constrains, and the command
transition it applies to. Values are the spec's speed-bin table entries;
"1KB/2KB page" variants depend on device organization. Clock conversion:
divide by tCK and round up (RU), unless the spec defines the parameter
directly in clocks.

## Row-cycle parameters

| Symbol | Definition | Applies between | Min (typ bins) |
| --- | --- | --- | --- |
| tRCD | Row-to-column delay: time for the row to reach the sense amps before a column command may execute | ACT(bank x) -> RD/WR(bank x) | 10-15 ns (800C/800D/800E); posted CAS still must land internal CAS at >= tRCD |
| tRP | Precharge recovery: sense amps and bitlines restored before re-activation | PRE(bank x) -> ACT(bank x) | 10-15 ns, bin-matched to tRCD; PREA on 8-bank parts: tRP + 1 tCK |
| tRAS | Minimum row-open time: data must be restored to the cells before precharge | ACT(bank x) -> PRE(bank x) | 45 ns min (40 ns DDR2-400B), 70 us max |
| tRC | Row cycle: full open-close-reopen loop for one bank | ACT(bank x) -> ACT(bank x) | tRAS + tRP; 55-60 ns at DDR2-800 |

## Activate-rate parameters (cross-bank)

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRRD | Activate-to-activate spacing, any two banks (limits peak array current) | ACT(bank x) -> ACT(bank y) | 7.5 ns (1KB page) / 10 ns (2KB page) |
| tFAW | Four-activate rolling window: at most 4 ACTs inside any window of this length (8-bank parts) | any 4 ACTs within a sliding window | 37.5 ns (1KB) / 50 ns (2KB) at 400/533/667; 35/45 ns at DDR2-800 |

tFAW example with the drill model: if RU(tFAW/tCK) = 10 and an ACT lands
at clock N, at most three more ACTs may land in clocks N+1 .. N+9.

## Data-to-precharge parameters

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRTP | Read-to-precharge: last 4-word read prefetch must complete internally before the row closes | RD(bank x) -> PRE(bank x) | 7.5 ns |
| tWR | Write recovery: last write data must be committed to the cells before precharge | end of WR burst(bank x) -> PRE(bank x) | 15 ns; programmed in clocks in MR, WR = RU(tWR/tCK), codes for 2-6 |
| tDAL | Write auto-precharge total: programmed WR plus precharge, before the bank may be re-activated | WRA(bank x) -> ACT(bank x) | WR + tRP (clocks) |

Command-spacing formulas that fall out of these (same bank):

| Transition | Earliest spacing (clocks) |
| --- | --- |
| RD -> PRE | AL + BL/2 + max(RU(tRTP), 2) - 2 |
| WR -> PRE | WL + BL/2 + RU(tWR) |
| RDA -> ACT | AL + RU((tRTP + tRP)/tCK) at BL4; +2 more at BL8; also >= tRC |
| WRA -> ACT | tDAL, also >= tRC |

The -2 in RD->PRE confuses everyone once: the spacing is measured from
the RD command, and the analog tRTP clock starts at the internal read
(AL clocks in), so the posted-CAS hold and the burst itself cover part of
it. For BL8 the internal read starts 2 clocks later relative to the burst
end, hence max(RTP, 2) and the BL-dependent forms.

## Why these four numbers dominate

tRCD and tRP are the row-miss penalty. tRAS + tRP = tRC bounds how fast
one bank can cycle rows. tRRD and tFAW bound how fast the whole device can
open rows regardless of how many banks are free - on activate-heavy
streams (many small transfers, open-page policy) tFAW is usually the
binding constraint, not tRRD. The controller's scheduler exists to hide
tRCD/tRP behind other banks' data and to pace ACTs against tRRD/tFAW.

**Source:** JESD79-2F sections 3.5, 3.7, 3.8, Tables 41-43
