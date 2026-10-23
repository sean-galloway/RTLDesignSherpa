# TASK-044: FR-FCFS core — dependent-hop latency (exact close-on-drain + next-op hint)

> Source: owner, 2026-10-23 — "Why is bank pick still beating fr-fcfs?"
> after BUG-030 removed the multi-thread collapse. Measured on the perf
> proxy with every scheduler fire logged (`PERF_CMD_TRACE=1`), one
> generator, txn 256, board geometry; mem-ctrl recovery Phase 3 report
> §5.4 has the histograms and the reading.
> Related: BUG-027 (closed; why pumice carries CLOSE_ON_DRAIN=0), BUG-030
> (the multi-thread half of the gap, fixed 488a9654c), granite's
> `mc_bank_pick` header (the mechanisms this task would port).

**Priority:** P2 (research SKU; the product core already has it)
**Status:** closed 2026-10-23 (DONE -- see "Result" below; board build-perf
75 MHz WNS +0.001, 0 / 86 323 failing endpoints on the committed text).
**Owner:** TBD

## What was measured (one thread, cycles; floor = the proxy's JEDEC model)

| item | BANK_PICK | FR-FCFS |
|---|---|---|
| col_major, cycles per 8-column row | 13 rd / 15 wr (= floor) | 24 |
| col_major, column gap at the row switch | 6 / 8 | 17 |
| col_ilv, cycles per row | 9-11 | 13 / 15 |
| incremental, gap at a row change | 2 | 6 / 8 (PRE and ACT as separate transits) |
| MB/s col_major / col_ilv / incremental (wr) | 310 / 459 / 568 | 194 / 306 / 551 |

## Why

1. **Explicit PRE.** pumice carries `CLOSE_ON_DRAIN = 0` since BUG-027:
   the arbiter's AP term reads "youngest in-window column of the
   (bank,row)" as "last demand" and chopped page-hit streams every
   NUM_ENTRIES bursts. With it off every row close is a PRE command that
   transits the pick pipeline.
2. **No lookahead / hint.** Each dependent hop (column -> PRE, PRE -> ACT,
   ACT -> column) is classified only after the timers show the previous
   fire, so each hop pays the three-stage pipeline. BANK_PICK's decode
   uses the timers' lookahead bits and a next-op hint from the fire stage
   and lands each hop on the floor; its ACT/PRE-versus-column alternation
   also slips another bank's row commands inside a column run, which is
   the col_ilv difference.

## Scope

- Replace the arbiter's AP predicate with the exact one `mc_bank_pick`
  uses ("no same-row entry, schedulable or filling, behind this column in
  its bank"), then re-enable CLOSE_ON_DRAIN for pumice and re-run the
  BUG-027 probe cells (they must stay green: that is the regression that
  turned the feature off).
- Add a next-op hint / lookahead classification to `mc_cmd_arbiter`
  (shape in the `mc_bank_pick` header), keeping the 75 MHz board floor
  (thin positive WNS is the design point).
- Exit: col_major one-thread within 1 cycle per row of the floor on
  FR-FCFS; incremental / row_major unchanged or better; pumice regression
  216 / 1 at both geometries; build-perf board build positive WNS.

## Not this task

The multi-thread residual at eight threads (464 / 493 vs the 554 / 553
timer-off ceiling) is the BUG-030 predictor re-learning, tracked there.

## Result (2026-10-23)

col_major one-thread: 24 -> 13 / 15 cycles per row = the floor (309 / 351
MB/s, was 195 / 194; BANK_PICK 311 / 358). Full table and the hop-by-hop
account: Phase 3 report section 5.5. What landed, in the order it was
measured:

1. Exact close-on-drain: `wr_sch_pend_i` (allocated, data not landed)
   counts as demand in `mc_cmd_arbiter`'s last-column detect and fire-stage
   sibling re-check; the storage plane exports `wr_sch_pend_o`; planes,
   cores, scoria / andesite, the store-arbiter bench and the formal harness
   carry the port. Row 24 -> 19 / 21.
2. Forward paths: column hit against the ACT being picked / in the output
   register / fired last cycle; early ACT behind a PRE being picked / in
   the output register / fired (`r_pre_closing`); ACT-only guard
   (`w_act_guard`); fire stage = live row match for columns
   (`w_col_row_ok`) plus bounded holds (tRCD via the lookahead bit, closed
   bank inside tRP / tRC, AP drain). Row 19 / 21 -> 13 / 15.
3. The close is armed per bank by `mc_page_policy` (`drain_close_ok_o`):
   a different-row ACT after a row of at most `DRAIN_ARM_MAX_COLS` (8)
   columns arms, a same-row reopen disarms, evidence only in fixed_open,
   RDA / WRA count as predicted closes. Without it the six BUG-027 cells
   fail with close-on-drain on (just-in-time AW invisible to any
   predicate), and without the mode gate the board-geometry paging sweep
   loses 17 % of its 8-bank window to static_close's history.
4. `CLOSE_ON_DRAIN` default 1 again in pumice_core / top / geared /
   ddr2_char_macro / harness / tb tops; `TEST_CLOSE_ON_DRAIN` (proxy) and
   `PUMICE_CLOSE_ON_DRAIN` (core_dfi, close_drain probe) override it.
   `test_pumice_close_drain` drives fixed_open / tr_init 2, expects the
   first rows per bank to close by the timer and judges steady state from
   the eighth ACT.
5. RDS-DV 92ec9bd: the DRAM model times an auto-precharge like the device
   (`on_auto_precharge`); the old shortcut reported one phantom tRTP / tWR
   per RDA / WRA. The write-recovery anchor phantom is ISSUE-023.

Gates: pumice 217 / 217 both geometries, granite 6 / 1 xfailed, common-ip
25 / 3 xfailed, formal prove PASS, lint clean on four cores, RDS-DV model
suite 46 / 46, board build-perf 75 MHz WNS +0.001 (0 / 86 323; LUTs 42 822
vs 41 063 before, FFs 33 985 vs 33 753). The first board build of the
forward paths missed by 2.2 ns because the pick-cycle hints were taken
from the pick comb (arg_sel + pick mux + fire-stage cone chained into the
classify cone); rebuilt from the pre-pick registers they are exact and the
floor holds. Not done here: the col_interleave write gap to BANK_PICK
(column-first class priority vs the per-bank core's alternation; an
alternation would chop the write runs the perf-shape cells pin) and the
multi-thread streaming residual (BUG-030 predictor re-learning; 464 -> 510
at eight threads from the faster hops alone).

