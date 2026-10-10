# Pumice Unified Prospect Pool — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans (native — the human partner has already chosen native execution for this workstream) to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Merge the rd/wr-duplicated classify/overlay/population logic in `pumice_cmd_arbiter` into a single `2N`-entry unified prospect pool, with a **bit-identical command stream**, as the pumice-side foundation for the Task-5 common scheduler (design approved by the human partner 2026-10-10: "let's try A then on pumice").

**Architecture:** The two CAMs stay split (their sinks differ: wr → data-drain commit, rd → AR-order issue). What unifies is the **prospect view** the pick pipeline reads: one concatenated `{dir, bank, row, col, qos, valid}` pool, one classify loop, one population-counter loop, one snapshot. Per-direction storage shapes (six masks, two pop arrays, snapshot registers) are preserved verbatim so every downstream consumer — the six `arg_sel` argmaxes, pre-pick flops, priority chain, fire stage, in-flight guard shadow, stall counters — is textually untouched. Fire-stage authority, the epoch snapshot, and all pipeline registers stay exactly where they are (the 4/5-merge was explicitly rejected: the output register is the timing authority, backpressure element, and BUG-003 fire==push guarantee).

**Tech Stack:** SystemVerilog (Verilator lint strict + cocotb DV), pumice existing suites as the behavior pin.

**Spec:** Design as approved in conversation 2026-10-10 (analysis message: merge stages 0/1/2's *logic*, keep all registers; do not merge 4/5); Phase-2 umbrella spec `docs/superpowers/specs/2026-10-09-mem-ctrl-ip-reorg-design.md`.

## Global Constraints

- **Bit-identical behavior.** Full pumice suite green before AND after with IDENTICAL pass counts (last recorded green: 98 macro / 215 top / 159 fub, Phase-2 Task 3, SEED=12345). No test may be modified, skipped, or re-pinned — including characterized perf floors (a perf-floor trip is a regression signal, not a re-pin opportunity; see pumice ISSUE-020 history).
- **One RTL file modified:** `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_cmd_arbiter.sv`. No port changes → scheduler layer, filelists, and all DV TBs untouched.
- Verilator lint clean via `make -C projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl lint` (cocotb builds are warning-fatal).
- DV env (from repo root, every run): `source env_python && export PYTHONPATH="$(pwd)/bin" PYTHONPYCACHEPREFIX=/tmp/pycache-prospect SEED=12345 && source venv-cocotb2/bin/activate`. `SEED=12345` is mandatory (deterministic default; the zq soak consumes the env var).
- Commits pathspec-limited; **never** stage foreign work: `formal/amber/*`, `formal/pumice/wr_data_cam/formal_wr_data_cam.sv` (another agent's), untracked `coverage_reports/`. Hooks run 60–400 s — use background + WaitFor, never `--no-verify`.
- TDD mapping for a pure refactor: the failing-test oracle is the existing suite. Baseline-green is established before touching RTL (by fresh smoke + byte-identity to the Task-3 green commit); after the refactor, any suite failure IS the red test proving behavior changed.

## Review Focus

The five input classes most likely to bite (each is a silent behavior change the suite's sched-order/turnaround/refresh tests are designed to catch — do not "fix" the test, fix the mask):

1. **Cross-direction population contamination** — `pop[i]` must count only same-direction entries sharing `{bank,row}` (today's per-CAM semantics). A merged pop changes `most_pending`/`fewest_pending` picks. Pinned by `sched_order_mode`/`row_sel`/`col_sel` tests.
2. **QoS narrowing across directions** — `qos_top` must run per direction slice; a WR's higher QoS must never narrow RD candidates (and vice versa). Pinned by `qos_en` tests.
3. **Turnaround direction mapping** — `w_rd_turn_block` (blocks RD, = tWTR side) applies to dir-0 entries; `w_wr_turn_block` (blocks WR, = tRTW side) to dir-1. An inverted mapping is the issue-#42/TASK-007 bus-contention class. Pinned by turnaround/sched-order soaks.
4. **Sink-ready mapping** — dir-0 (RD) gates on `rd_issue_ready_i`, dir-1 (WR) on `wr_commit_ready_i`. Swapped = the "column fires while its CAM refuses it" class (double-issue + misrouted return / stale-DRAM write). Pinned by concurrent-rd/wr soaks and CAM drain tests.
5. **Argmax tie-break order** — `arg_sel`'s high-index-wins-among-one-hot iteration must be preserved exactly; achieved by slicing the pool masks back into the existing per-direction mask names and NOT re-indexing the argmaxes. Pinned by deterministic sched-order golden sequences (fixed SEED).

---

### Task 1: Baseline

**Files:**
- Modify: none.

**Interfaces:**
- Produces: recorded green baseline — arbiter file byte-identical to the Task-3 green commit; scheduler smoke tests fresh-passing at HEAD; recorded suite counts to compare against.

- [ ] **Step 1: Prove the arbiter is the byte-identical, suite-green version.** `git diff 6c8cc9e8 -- <arbiter>` must be empty (6c8cc9e8 = Phase-2 Task-3 full-suite gate); `git log --oneline -1 -- <arbiter>` records its last touch. Grep pumice filelists/DV for `compute-eng-ip` (stale after the riscv-ip rename): `grep -rn "compute-eng-ip" projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/ --include="*.f" --include="*.toml" --include="*.py" | head` — expect no hits.
- [ ] **Step 2: Fresh scheduler smoke at HEAD.** From repo root with the DV env: run the scheduler-layer + cmd-arbiter tests (glob `dv/tests/**/test*pumice*sched*.py`, `test*pumice_cmd_arbiter*.py` under the pumice rock; fall back to the `fub` scheduler subset if no dedicated arbiter TB). Expected: PASS. This is the fresh half of the baseline (the full suite's last green is documented in the Phase-2 ledger; a fresh full pre-run is not required given Step 1's byte-identity, and editing while a full run compiles from the tree would corrupt it).
- [ ] **Step 3: Record baseline in the ledger.** Append a Task-4.5 entry to `.superpowers/sdd/2026-10-10-mem-ctrl-ip-phase2-common-extraction/progress.md` noting: insertion approved by partner, arbiter byte-identity proof, smoke result, target counts (98/215/159).

### Task 2: Refactor — merged pool classify + population

**Files:**
- Modify: `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_cmd_arbiter.sv` (only).

**Interfaces:**
- Consumes: all existing guard/timing signals (unchanged definitions): `w_guarded`, `w_col_inflight_bank`, `r_ap_closing`, `w_rd/wr_col_inflight_ent`, `w_ref_col_block`, `w_rd/wr_turn_block`, `w_ap_col_guard`, `w_pre_col_guard`, `w_preact_bank_guard`, `w_act_classify_gate`, `w_rfc_busy`, `w_tccd_fwd_ok`, `r_bank_*` image, `f_ap`.
- Produces (names downstream already consumes — MUST NOT change): `rd_col_m/rd_act_m/rd_pre_m`, `wr_col_m/wr_act_m/wr_pre_m`, `rd_pop[]/wr_pop[]`, and through the untouched overlay/snapshot path `rd_*_me`, `rd_*_q`, `r_rd_*_q`, `r_rd_older`, `r_col_sel/r_row_sel`, `r_ap_snap`. New internal-only: `pool_*` concat vectors, `PTXW`, pool extractors.

- [ ] **Step 1: Add the pool plumbing** (immediately after the `f_bank/f_row/f_col` extractors, ~line 701):
  - `localparam int POOL = 2*NUM_ENTRIES; localparam int PTXW = PTRW+1;`
  - Concatenated views: `pool_valid = {wr_sch_valid_i, rd_sch_valid_i}`, `pool_bank = {wr_sch_bank_i, rd_sch_bank_i}`, `pool_row`, `pool_col` (same pattern). Direction test per entry: `dir = (e >= NUM_ENTRIES)`, within-direction slot `i = dir ? e-NUM_ENTRIES : e`.
  - Pool extractors `f_pool_bank/f_pool_row/f_pool_col` taking `input logic [PTXW-1:0] e` against the pool vectors (the existing `f_*` take `PTRW` — do not widen them; Verilator is strict about width).
- [ ] **Step 2: Replace the two classify halves with one pool loop.** Replace the `always_comb` at lines 706–790: one loop `for (int e = 0; e < POOL; e++)` computing `hit`, then `pool_col_m[e]`, `pool_act_m[e]`, `pool_pre_m[e]` with the direction-conditioned column terms exactly as:
  - `pool_col_m[e] = hit && r_bank_rdwr_ready[RK0][bank] && w_tccd_fwd_ok && (dir ? trtw_ok_i : twtr_ok_i) && (dir ? wr_commit_ready_i : rd_issue_ready_i) && !(f_ap(bank) && w_col_inflight_bank[bank]) && !r_ap_closing[bank] && !(dir ? w_wr_col_inflight_ent[i] : w_rd_col_inflight_ent[i]) && !w_ref_col_block[bank] && (dir ? !w_wr_turn_block : !w_rd_turn_block) && !w_ap_col_guard[bank] && !w_pre_col_guard[bank] && !w_preact_bank_guard[bank]`
  - `pool_act_m[e] = !r_bank_row_active[RK0][bank] && !w_guarded[bank] && r_bank_act_ready[RK0][bank] && w_act_classify_gate && !w_rfc_busy`
  - `pool_pre_m[e]  = r_bank_row_active[RK0][bank] && !w_guarded[bank] && !hit && r_bank_pre_ready[RK0][bank]`
  - Each gated by `pool_valid[e]` exactly as today's `if (rd_sch_valid_i[e])` / `if (wr_sch_valid_i[e])` gating. Term-for-term this IS today's rd/wr expressions with `rb`/`wb` unified to `bank` and the four direction-conditioned terms multiplexed — no term may be added, dropped, or reordered in effect.
  - Declare `logic [POOL-1:0] pool_col_m, pool_act_m, pool_pre_m;` and slice-assign: `assign rd_col_m = pool_col_m[NUM_ENTRIES-1:0];` … six assigns (packed slices — safe in SV/Verilator).
- [ ] **Step 3: Merge the population counters.** Replace the two loops at 925–940 with one loop over `e in [0,POOL)`: count `j in [0,POOL)` where `pool_valid[j] && ((j>=NUM_ENTRIES) == dir_e) && bank/row match`; write the result into `rd_pop[i]` or `wr_pop[i]` per `dir_e`. Same-direction restriction is the bit-identity requirement (Review Focus #1).
- [ ] **Step 4: Do NOT touch** (list is contractual): `arg_oldest`, `arg_sel`, the six STAGE-1b argmax calls (they keep reading `r_rd_*_q`/`r_wr_*_q`, `r_rd_older`/`r_wr_older`, `rd_pop`/`wr_pop`), the ORDER_MODE overlay, `qos_top` calls, the STAGE-1a snapshot flop block, pre-pick flops, write-batching drain, class-priority chain, refresh/training/timeout branches, output register, `w_out_safe`/`w_out_hold`/`w_out_reject`, cmd push outputs, evt strobes, CAM commit/issue/grant strobes, ALL guard shift registers (`r_guard*`, `r_preguard*`, `r_apguard*`, `r_*fire*`, `r_ap_closing`), tRFC counter, stall-cause counters, in-flight shadow matrix. If any of these "needs" a change to compile, the pool wiring is wrong — fix the wiring, not these.
- [ ] **Step 5: Lint.** `make -C projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl lint` — clean (repo lint is `-Wno-fatal`; then ALSO compile-check strict by running the Step 6 smoke, which builds with warnings-fatal).
- [ ] **Step 6: Scheduler smoke post-refactor.** Same tests as Task 1 Step 2. Expected: PASS, identical.

### Task 3: Full gate + commit

**Files:**
- Modify: `.superpowers/sdd/2026-10-10-mem-ctrl-ip-phase2-common-extraction/progress.md` (ledger entry).

**Interfaces:**
- Consumes: Task 2's lint-clean, smoke-passing refactor.

- [ ] **Step 1: Full pumice suite.** `make -C projects/components test-mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2` from repo root with the DV env. Expected: PASS with counts identical to baseline (98 macro / 215 top / 159 fub at last recording — use the counts actually recorded at Task-1/2 time). Any failure: A/B debug against the pre-refactor file (`git stash` / `git show HEAD:<arbiter>`), NOT test edits.
- [ ] **Step 2: Repo gates.** `python3 bin/filelist_registry.py --check` and `--audit`; `python3 bin/check_broken_links.py --list`; `python3 bin/check_task_ids.py`. (No filelist change is expected; these catch accidents.)
- [ ] **Step 3: Commit.** `git status --short | grep -E '^[MA]' | grep -v mem-ctrl-ip` must show ONLY the known foreign entries (`formal/pumice/wr_data_cam/...`). Stage ONLY the arbiter + this plan + the ledger. `export PATH="$(pwd)/venv/bin:$PATH"` for hooks; commit message `refactor(pumice): unify sched CAM prospect pool — merged rd/wr classify/pop (bit-identical)`. Background + WaitFor (hooks are slow).
- [ ] **Step 4: Ledger close-out.** Task-4.5 entry: what merged, what was proven (byte-identity, smoke, full counts), line delta, and the note that this pre-empts part of Task 5's pumice-side dedup. Then resume Phase-2 Task 4 (training-layer shell) as the next action.

## Self-Review

1. **Spec coverage:** the approved design = merged classify/overlay/pop/snapshot (done in Task 2), registers kept (contractual don't-touch list), 4/5 not merged (architecture section states why)..
2. **Step scan:** each step names exact lines, exact signal names, exact expressions for the three merged masks. The implementer writes loop syntax only..
3. **Type consistency:** `pool_*` are packed `[POOL*x-1:0]`; extractors use `PTXW`; all produced names match existing downstream consumption (verified against file lines 890–1148)..
4. **Review Focus:** all five have named pinning tests in the suite (sched_order, qos, turnaround soaks, CAM drain, golden sequences)..
5. **Proportion:** plan ≈ design decisions; no full bodies transcribed beyond the three mask expressions, which the spec (bit-identity) fixes verbatim..
