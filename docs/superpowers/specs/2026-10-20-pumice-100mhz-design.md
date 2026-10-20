# PUMICE 100 MHz Convergence — Design Spec

Date: 2026-10-20
Status: approved design, pending implementation plan
Scope: `research-ip/pumice-ddr2-lpddr2` + shared `common-ip` modules it
instantiates. Granite is **frozen**: no granite-specific edits, no granite
validation. (Note for the record: `mc_cmd_arbiter` and the DFI fubs are
shared with granite; changes land in granite's build tree but granite is not
part of this work.)

## 1. Goal and success criteria

Pumice closes timing on the Nexys A7 part (xc7a100tcsg324-**1**) at
**aclk = 100 MHz, dfi_clk = 200 MHz, WNS ≥ 0 in both domains**, measured with
the established OOC flow (`synth_design` + async clock groups, artifacts under
`/tmp/pumice_timing_head/`, bucketized via `bin/vivado_timing_failures.py`),
and:

* `make run-all-func` green at both geometries (current bar: 216 passed /
  1 skipped (`test_pumice_close_drain`, skip-gated) / 78 lint).
* Char perf suite (`TEST_TREFI=585 TEST_TXN=1024`) shows no regression vs the
  recorded pre-change baselines: pass band is bw within ±2% and read/write
  latency within ±5 ns of baseline per cell, unless the pre-change run's own
  variance (recorded in the plan) justifies a different threshold.
* Zero-bubble steady-state command issue: the pick restructure must not add
  idle cycles in streaming page-hit traffic (owner decision 2026-10-20).

Latency budget note: the read-return path may grow by at most ~1 dfi_clk
cycle (5 ns PHY-side) from the aligner skid (§4). Everything else must not
add user-visible latency.

## 2. Baseline (HEAD `a8331c9d6`, OOC run 2026-10-20)

518 failing paths (aclk 100, dfi_clk 418), worst **−13.245 ns** (aclk),
dfi_clk worst −2.839 ns. Cone table (durable copy:
`research-ip/pumice-ddr2-lpddr2/debug/timing_failures_pumice_100mhz.xlsx`):

| Cone | Paths | WNS (ns) | Domain |
|---|---|---|---|
| FRFCFS pick core internal (pop → classify → `r_*_q` masks) | 55 | −13.25 | aclk |
| bank timers → pick core | 43 | −2.34 | aclk |
| rd aligner `r_age`/outstanding → rd CDC FIFO full | 362 | −2.84 | dfi_clk |
| rd aligner own credit/outstanding | 17 | −2.55 | dfi_clk |
| wr serializer → wrdata CDC FIFO | 3 | −2.27 | dfi_clk |
| cmd FIFO → wr-staged token FIFO | 2 | −1.13 | dfi_clk |
| DFI cmd FIFO → formatter output regs | 32 | −0.65 | dfi_clk |
| snarf data (wr_cam → rd_intake) | 1 | −0.01 | aclk |

The aclk disease is a state-heavy comb loop, not wire delay (worst path
22.4 ns of which 17.9 ns predicted route across 31 logic levels; both aclk
cones share the classify structure). The dfi_clk disease is the aligner
admission/capture state fanning into the async FIFO full-flag/push cone.

Current pick pipeline (from RTL): CAM flop vectors → comb classify (pool
build, tCCD-forward, turnaround, AP guard, REF recovery, bank/global
readiness, age-matrix oldest) → registered class masks `r_*_q` → comb
`arg_oldest` → output decision regs (`rd_col_f`/`wr_act_f`/… + slots) →
fire. Existing final-stage live JEDEC re-check with drop-on-reject and
rank-global ACT hold (`w_out_hold`) is correct and stays.

## 3. aclk pick-core restructure (`mc_cmd_arbiter`) — owner-mandated shape

**Known-ahead winner, zero bubbles, hold-on-not-fired.**

1. **Push-side pre-decode.** Per-entry class qualifiers that do not depend
   on live JEDEC state are computed once, when the entry is pushed/filled
   in the storage plane (wr_data_cam / rd_cmd_cam side), and stored as bits
   alongside the entry (exact host module is an implementation decision
   inside the plan; the constraint is *computed once per push/fill, never
   in the pick cone*). Candidates: bank/row/col structure decode,
   page-policy column eligibility, agg/last class, age-order inputs.
2. **Two registered stages cap cone depth.**
   *Stage A* — pool qualification vs the **registered** bank image
   (`r_bank_*` advisory image already pipelined at the arbiter input):
   `mask_A = valid && !done && precomputed_class && bank_image_ok` →
   flopped `r_cls_a`. *Stage B* — live-window overlay (turnaround,
   tCCD-forward, AP/REF guards) + age-matrix oldest select → flopped
   `r_pick_next` (winner index + class + slot). Each stage's comb depth
   must be ≤ ~60% of the 10 ns period at synthesis; OOC iteration proves it.
3. **Zero-bubble speculation.** `r_pick_next` is computed assuming the
   current `r_pick` fires: `pool_next = pool − {r_pick if popping}`. The
   speculative cone is mask-minus-one + oldest-select only — the row/col
   payload **never** passes through it. Payload is read from the CAM flop
   arrays by the registered winner index into the existing output decision
   regs (shallow index mux, off the critical loop).
4. **Hold-on-not-fired.** Fire keeps the existing live re-check authority.
   Gate fails → hold `r_pick` (winner stays, no recompute, no bubble when
   the gate opens); gate passes → `r_pick ← r_pick_next`, output payload
   regs update from the CAM arrays. Fresh-push decision latency must not
   exceed the current 2-cycle push→decision depth.
5. **Bank-timer feed.** Stage A's registered input absorbs the
   bank-timer→pick cone. Implementation must re-verify the
   `CLOSE_ON_DRAIN` tracker (default off in pumice; feature stays
   parameter-gated) does not re-create a live timer→classify path; the
   fire-stage live re-check remains the correctness backstop.

## 4. dfi_clk read aligner (`mc_dfi_rd_aligner` + rd CDC FIFO) — skid decouple

Insert a small (1–2 entry) `dfi_clk` skid between the aligner capture side
and the `gaxi_fifo_async` rd FIFO push:

* Aligner captures words into the skid on word-valid + credit **without**
  the FIFO full flag in the cone; skid→FIFO drain handles full. This cuts
  the `r_age`/`r_outstanding` → full → push-enable loop (362 paths).
* The async FIFO's own wr_ptr/full cone stays internal to `gaxi_fifo_async`;
  if OOC shows it still failing at 5 ns, the plan may register the full
  sampling one dfi_clk (explicit owner-visible decision point — this is the
  ~5 ns return-latency note in §1).
* `rd_ret_busy_o` / `op_ready_o` semantics (refresh read-window tracking)
  must be preserved exactly; unit tests for the aligner and the
  refresh/read-window probes are the guard.

## 5. Explicit non-goals

* No granite edits or granite validation of any kind.
* No change to `CLOSE_ON_DRAIN` default (pumice stays 0; feature intact).
* No AXI-plane or wr-path (excluding §4's shared-FIFO note) changes; the
  wrdata/token cones (3/2 paths, −2.27/−1.13 ns) are inside the async FIFOs
  and are expected to fall out with the aligner-side full-flag handling —
  if they do not, they get the same skid treatment in the plan.
* No SystemVerilog assertions in RTL (repo rule); checkers live in TBs.
* No board programming (owner's call, as always).

## 6. Verification gates (all must pass, in order)

1. Unit: arbiter/scheduler, aligner, CDC, CAM tests.
2. `make run-all-func` both geometries — 216 passed / 1 skipped / 78 lint.
3. Char perf suite vs recorded baselines (`TEST_TREFI=585 TEST_TXN=1024`);
   single- and multi-bank rd/wr, row_major, col_major.
4. OOC 100 MHz: WNS ≥ 0 both domains; bucketized xlsx + updated red-cone
   annotations in `research-ip/pumice-ddr2-lpddr2/debug/` diagrams.
5. Report: WNS table, perf delta table, and the granite-inheritance note
   (which common-ip modules changed) for the owner's granite-spec session.

## 7. Risks

* **Scheduling-behavior drift**: the restructure could change corner-case
  pick order (order modes, QoS overlay). Guard: func suite + perf suite;
  any cell outside noise is a stop-and-report, not a tweak.
* **Shared-module inheritance**: granite builds pick up the new
  `mc_cmd_arbiter`; granite's own cones may shift. No action; recorded.
* **Residual WNS**: if Stage A/B still miss 0 after iteration, the fallback
  is narrowing Stage B's oldest-select (per-bank pre-rank at push) — stop
  and report rather than silently deepening pipelines.
