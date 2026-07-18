# pumice perf fix + regression gates — implementation spec

From the on-board characterization (2026-07-08): ~12.7 MB/s FLAT across access
pattern, page policy, and burst length (bl=1..64) — ~2% of DDR2 peak. Root cause
+ fix surface below, confirmed by RTL + DV exploration. Direction (user):
**no policies at compile time — all runtime**; gates include real-timing BW.

## Root cause
1. **PAGE_POLICY is compile-time and hardwired CLOSE** (`macro/pumice_core_macro.sv:49`,
   `top/pumice_top.sv:77`, `fub/scheduler.sv:61`). The scheduler's `w_initial_state`
   (scheduler.sv:437) and `w_ap_for_rdwr` (scheduler.sv:451) read the *parameter*,
   not the runtime CSR — so `REFRESH_TUNING.page_policy_or` is INERT (confirmed on
   silicon: OPEN==CLOSE). CLOSE forces RDA/WRA (auto-precharge) every command →
   no row-hit batching → every 8-byte AXI beat = ACT+CAS+PRE.
2. **Scheduler issues one DRAM command per ~4-cycle FSM pass** (S_IDLE→S_NEED_ACT→
   S_NEED_RDWR→S_DONE, scheduler.sv:502-755), gated on `cmd_ready_i`. No multi-
   command/bank-parallel issue → burst length gives zero pipelining gain.
3. **Read wedge ~4790 txn**: `rd_cmd_cam.r_beats_returned` is 8-bit (`fub/rd_cmd_cam.sv:126`)
   and 16 slots; entry_complete (`:159`) can't retire under sustained load →
   push_ready low → axi_intake wedges. Widen counter + revisit retire path.

## Fix (this task) — make page policy RUNTIME
`cfg_page_policy_or` already exists (config_block `macro/pumice_config_block.sv:191`
from `REFRESH_TUNING.page_policy_or`) and rises to `pumice_top` (`:486/:529`) but is
NEVER threaded down. Thread it: **pumice_top → pumice_core_macro → command_scheduler_macro
→ scheduler**, and in the scheduler compute the effective policy:

    // CSR page_policy_or: 0=use reset default, 1=OPEN, 2=CLOSE, 3=HYBRID
    // pumice_pkg enum:    OPEN=0, CLOSE=1, HAPPY_HYBRID=2
    logic [1:0] w_eff_policy;
    assign w_eff_policy = (cfg_page_policy_or == 2'd0) ? PAGE_POLICY[1:0]
                                                       : (cfg_page_policy_or - 2'd1);

Use `w_eff_policy` in place of `PAGE_POLICY` at scheduler.sv:437 and :451. The
`PAGE_POLICY` param is DEMOTED to only the reset default (CSR=0). `predict_open_i`
(HAPPY_HYBRID) is already a runtime input, so HYBRID works once selected. Ports to
add (all `input logic [1:0] cfg_page_policy_i`): scheduler, command_scheduler_macro
(pass to `.cfg_page_policy_i` on u_scheduler), pumice_core_macro (pass down),
pumice_top (wire the existing `cfg_page_policy_or`). Update the FUB TB
`dv/tbclasses/scheduler_tb.py` to drive the new input (0 = keep param default →
existing test_scheduler.py behavior unchanged).

Follow-ons (separate tasks, larger): (b) multi-issue/bank-parallel scheduler FSM
for intra-burst pipelining; (c) widen rd_cmd_cam counter to kill the ~4790 wedge;
(d) thread scheme/lookahead the same way (scheme_active_i is already runtime).

## Regression gates (perf-TDD) — FAIL if targets not met
Add to `dv/tests/macro/test_pumice_core_macro.py` a `perf_page_batching` scenario.
Reuse the existing `SchedulerTracker` (`dv/tbclasses/trackers/scheduler_tracker.py`
`stats()` gives `col_ops_with_ap` / `col_ops_open_page` / `per_bank_act_counts`).

1. **Command-efficiency (timing-independent, works in zero-latency sim):**
   - Same-row streaming workload (many bursts to one open row).
   - Drive `cfg_page_policy_i = OPEN`; assert `col_ops_open_page` dominates and
     `acts_per_read = ACT/RD <= 0.25` (page batched under one ACT). **RED today**
     (policy inert → all RDA → acts_per_read ~1.0), GREEN after the fix.
   - Drive `cfg_page_policy_i = CLOSE`; assert AP ratio > 0.8 (policy actually
     switches — proves runtime control).
2. **Real-timing bandwidth (user-requested):** enable DRAM timing in the DFI BFM
   — `dv/tbclasses/pumice_core_macro_tb.py:158` currently sets
   `ViolationPolicy(hard=frozenset())` (zero-latency). Add a perf variant that
   enforces tRCD/tRP/tRAS/tRC (DramStateModel with a non-empty hard set / a
   latency-modeling responder) so cycles-per-beat is real, then gate:
   `cycles_per_beat(OPEN, same-row) <= TARGET` and assert OPEN << CLOSE. This is
   the metric that would have caught the 12.7-flat on the bench.

Pattern B (cocotb_test_* + pytest wrapper). Wire in the sched tracker exactly as
`patho_addr_pattern` does (test_pumice_core_macro.py:338-351).

## Task 1 (next) — issue-per-cycle scheduler (no FSM), safe-timer gated
Replace the one-op-in-flight FSM (scheduler.sv: S_IDLE→S_NEED_PRE→S_NEED_ACT→
S_NEED_RDWR→S_DONE→S_IDLE, ~4 cyc/op, no bank parallelism) with: **each clock,
issue one command to the best slot whose next-needed command is SAFE now.**
"Safe" = the JEDEC timers that already exist as scheduler inputs:
`bank_act_ready_i` (tRCD/tRP/tRC/tRRD via xbank_timers) + `tfaw_window_ok_i` for
ACT; `bank_pre_ready_i` (tRAS/tWR/tRTP) for PRE; `bank_rdwr_ready_i` (tCCD/tWTR/
CL/CWL/bus turnaround) for RD/WR; `cmd_ready_i` for the formatter. Per-slot needed
command from the existing `w_initial_state` logic vs `bank_row_active_i`/
`bank_open_row_i`. Issuing fires `evt_act/pre/rd/wr` (advances xbank_timers next
cycle) and, on RD/WR only, `*_issued_we` (retires the CAM slot).

Two hazards MUST be handled:
1. **Timing closure (~0 slack today).** A flat combinational "issuable" check
   over all 16 slots x 8 banks + a single-cycle pick will likely miss 100 MHz.
   Keep the pick PIPELINED (extend the existing registered candidate tree to be
   readiness-aware: fold each slot's "needed-cmd-ready" into the tree's validity
   so the winner is the best *issuable* slot), issuing the registered winner next
   cycle. Preserves the timing structure that closes today.
2. **Double-issue.** `*_issued_we`→CAM `r_issued` is registered (1-cyc late); the
   FSM round-trip hid this. Add a 1-cycle "just-issued slot" bypass mask that
   combinationally excludes the slot issued last cycle from the candidate set,
   so it isn't re-picked before `r_issued` propagates. (test_command_scheduler_macro
   `no_double_issue_race` guards this.)

Keep S_IDLE's init/refresh/MR/PDN injection priority (those still gate the bus).
ACT does NOT retire a slot; only RD/WR does — a slot needing ACT is picked,
issues ACT, then next cycle (after tRCD) is row-hit and issues its RD/WR. While it
waits tRCD, the readiness-aware picker issues a DIFFERENT bank's ACT → the
bank-level parallelism + pipelining that turns ~63 cyc/beat into back-to-back.

Verify (functional AND timing — this is arbitration-core + knife-edge timing):
- `test_command_scheduler_macro.py` incl. `no_double_issue_race` (no double-issue)
- scheduler FUB suite (timing-correctness checkers) + macro integrity suites
- perf gate: extend perf_page_batching to assert commands issue back-to-back
  (e.g. ACT(bankB) overlaps tRCD(bankA)); add the real-DFI-timing cycles/beat gate
- **Vivado STA**: `make bitstream` (or synth) — WNS must stay >= 0 (we're at ~0).

## Verify
    source env_python
    # RED (before fix): the OPEN gate fails — policy inert
    pytest dv/tests/macro/test_pumice_core_macro.py -k perf_page_batching -q
    # after fix: GREEN; and existing suites still pass
    pytest dv/tests/fub/test_scheduler.py -q
    pytest dv/tests/macro/test_pumice_core_macro.py -q
