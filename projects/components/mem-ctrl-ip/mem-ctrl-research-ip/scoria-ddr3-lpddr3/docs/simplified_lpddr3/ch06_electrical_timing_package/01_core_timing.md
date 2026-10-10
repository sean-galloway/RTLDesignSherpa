# Core Timing Parameters

The bank-state timings: what each parameter constrains, and the command
transition it applies to. Values are from the AC timing table (Table 64);
clock conversion is divide by tCK(avg) and round up (RU).

## Row-cycle parameters

LPDDR3 carries TWO precharge times - one per-bank, one all-bank - and the
choice follows the command, not the register:

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRCD | Row-to-column delay; three speed grades exist (fast/typ/slow) | ACT(bank x) -> RD/WR(bank x) | max(15/18/24 ns, 3 nCK) |
| tRPpb | Precharge recovery, single bank | PRE(bank x) -> ACT(bank x) | max(15/18/24 ns, 3 nCK) |
| tRPpab | Precharge recovery, all banks | PREA -> ACT(any) | max(18/21/27 ns, 3 nCK) |
| tRAS | Minimum (and maximum) row-open time | ACT(bank x) -> PRE(bank x) | min max(42 ns, 3 nCK); max min(70.2 us, 9 x RM x tREFI) |
| tRC | Full row cycle; built from whichever precharge applies | ACT(bank x) -> ACT(bank x) | tRAS + tRPpab, or tRAS + tRPpb |

The fast/typ/slow tRCD and tRP grades are a low-power knob: a slower
setting eases the analog timing budget (and saves power) at the cost of
latency. The tRAS maximum is where the refresh multiplier RM (MR4) shows
up in scheduling math.

## Activate-rate parameters (cross-bank)

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRRD | Activate-to-activate spacing, any two banks (limits peak array current) | ACT(bank x) -> ACT(bank y) | max(10 ns, 2 nCK) |
| tFAW | Four-activate rolling window: at most 4 ACTs (or REFpb) inside the window | any 4 ACTs within a sliding window | max(50 ns, 8 nCK) |

The spec's own window example: if RU(tFAW/tCK) = 10 and an ACT lands in
clock n, at most three more ACTs may land in clocks n+1 .. n+9. Note
tFAW counts REFpb as well as ACT - per-bank refresh consumes activate
budget.

## Data-to-precharge parameters

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRTP | Internal analog read must finish before the row closes | last read data(bank x) -> PRE(bank x) | max(7.5 ns, 4 nCK) |
| tWR | Write recovery: last write data committed to the cells before precharge | last write data(bank x) -> PRE(bank x) | max(15 ns, 4 nCK) |

Command-spacing formulas that fall out of these (same bank):

| Transition | Earliest spacing (clocks) |
| --- | --- |
| RD -> PRE | BL/2 + max(4, RU(tRTP/tCK)) - 4 |
| WR -> PRE | WL + BL/2 + RU(tWR/tCK) + 1 |
| RDA/WRA -> ACT | precharge fires automatically after the recovery window; next ACT >= tRP after it actually starts, and >= tRC from the old ACT |

## Why these numbers dominate

tRCD and tRP are the row-miss penalty - and LPDDR3 makes the controller
choose per precharge whether it pays tRPpb or the larger tRPpab.
tRAS + tRP = tRC bounds per-bank row cycling; tRRD and tFAW bound device-
wide activate rate, with tFAW also metering per-bank refreshes. The
scheduler hides tRCD/tRPpb behind other banks' data and paces ACTs (and
REFpBs) against tRRD/tFAW.

**Source:** JESD209-3C sections 4.1, 4.7, 11.4 (Table 64)
