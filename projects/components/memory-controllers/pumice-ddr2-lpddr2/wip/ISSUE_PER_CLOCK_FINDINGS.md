# Issue-per-clock (bank-parallel) scheduler — findings + blocker

Status: **WIP, not instantiated.** `wip/scheduler_bankparallel_wip.sv` is a
complete per-bank-machine + arbiter rewrite of `rtl/fub/scheduler.sv`. It is
correct in isolation but is blocked by a data-path ordering contract. The
committed `rtl/fub/scheduler.sv` (single-op FSM + runtime page policy) is
unchanged and remains the shipped design (validated 8.8x streaming, see
char_results/FINDINGS_page_policy_ab).

## What the WIP does
Replaces the one-op-in-flight FSM with **per-bank op machines + a shallow
per-cycle arbiter**, reusing the proven 2-stage pipelined QoS/age tournament
(gated with a bank-busy + just-issued mask). Each bank tracks its own phase
(PH_PRE -> PH_ACT -> PH_RDWR) locally, so ACT/PRE for different banks overlap
(hiding tRCD/tRP) while the arbiter issues one command/cycle. Includes a
command-hold lock (stable command across the DFI valid/ready handshake) and
injection gating.

## Verification reached (all GREEN)
- scheduler FUB suite: **23/23** (exact-cycle contract + invariants preserved —
  the per-bank pipeline depth happens to match the old FSM's timing).
- command_scheduler_macro: **3/3** (incl. no_double_issue_race).
- pumice_core_macro perf_page_batching[OPEN] + [CLOSE]: **2/2** (after fixing a
  refresh-forces-reACT wedge — REF doesn't precharge the bank in the timer model,
  so forcing PH_ACT waited on bank_act_ready forever; removed that block).
- pumice_core_macro smoke + ~75/109 of the full matrix.

## UPDATED root cause (waveform-traced): a slot-reuse RACE

Traced the smallest clean reproducer **`id_fixed_7_n64`** (N=64 same-id-7 BL4
bursts, all one bank/row; run it alone with a wiped sim_build). Instrumenting the
scheduler's accepted-command stream + bank-machine state showed:

- The command stream is otherwise textbook and in-order (bank 0, reused slot 0,
  cols 0,4,8,… each ACT then RDA/WRA) — NOT the cross-bank reordering first
  suspected.
- Exactly ONE op is lost per run: e.g. read col 24 gets its ACT but its RDA
  never issues (the op leaves the bank machine without retiring), so only 63/64
  RDAs issue. The in-order read aligner then shifts every later burst → the
  localizer flags a much later burst (e.g. 51). Other runs instead drop/​corrupt
  a WRITE byte.
- **It is nondeterministic**: adding/removing a debug `$display` moves the failure
  (read-drop ↔ write-byte-corruption ↔ passing). Threshold is N > CAM depth (16)
  — i.e. it only appears once slots are REUSED.

Interpretation: the bank-parallel scheduler retires an op and lets axi_intake
re-allocate the same CAM slot (slot 0, one-outstanding here) FASTER than the
previous op's completion machinery drains (issued_we → CAM r_issued → b_complete
/ rd_beat retire are all registered, multi-cycle). The old ~4-cyc/op FSM never
reused a slot that fast, so the window was never hit. Under fast reuse there is a
1-op-wide window where the new occupant of a slot is clobbered / its beat count
mis-tracked → one op silently lost. This is a scheduler ↔ wr_cmd_cam/rd_cmd_cam/
axi_intake timing contract, not pure AXI reordering.

Sharp next step for the fix (data-path co-design, the chosen path): make slot
free→reallocate safe under back-to-back reuse — e.g. the CAM must not present a
slot as free-for-reallocation until its prior occupant has fully retired
(issued + b_complete/rd_beat drained), OR the scheduler must not re-pick a slot
index until its completion has propagated (extend the just-issued shadow to cover
the full retire latency, and/or gate reuse on a per-slot "fully drained" bit from
the CAM). The reproducer `id_fixed_7_n64` deterministically stresses the window;
add a scheduler-level assertion "every issued op eventually retires exactly once"
to catch the lost op directly instead of via downstream data corruption.

## (Earlier hypothesis) AXI per-id ordering vs bank-parallel column issue
34/109 core-macro tests fail with WR/RD PATH CORRUPTION (a beat returns 0x00;
the DRAM memory model has the correct value but the AXI read returns 0, or a
write beat never lands). Failing set: engine_mirror at scale, hit_miss
oscillation, profile_sweep with backpressure — including **fixed-id** patterns.
Corruption is **deterministic** (the arbiter is deterministic).

Root cause: **pumice's data path assumes column-op issue order == completion
order per AXI id** (rd_cl_aligner / axi_intake R-emit / b_fifo have no per-id
reorder buffer). The bank-parallel arbiter issues in age (arrival) order EXCEPT
when an older same-id op's bank is not yet `bank_rdwr_ready` (still activating)
while a younger same-id op's bank IS ready — the younger op jumps ahead ->
out-of-order same-id completion -> the in-order data path mis-reassembles ->
zeroed beats. The old FSM never reordered (strictly one op, in pick order).

Secondary (masked by the above): the write beat sequencer shares ONE w_buf pull
port (1 beat/cyc) feeding a drive at DFI_RATE beats/cyc; >1 concurrent write op
underruns. Serializing writes (MAX_CONCURRENT=1) did NOT fix the corruption
(confirming ordering is the primary cause) and introduced timeouts, so it was
reverted.

## Options (for the user to scope)
1. **Data-path co-design (the real unlock):** add a per-id read reorder buffer
   (or per-id completion tracking) in rd_cl_aligner / axi_intake, and relax the
   write-pull capacity (wider pull port or per-op staging), so out-of-order
   column completion is safe. Unlocks full bank-parallel column throughput
   (~1 cyc/beat + random-access parallelism). Largest effort.
2. **Constrained scheduler (moderate):** keep bank-parallel ACT/PRE prep but
   issue column (RD/WR) ops strictly in global age order (a per-direction
   "oldest-issuable-only" interlock). Correct with today's data path. Helps
   ACT-heavy patterns (CLOSE / random — hides tRCD/tRP) but NOT OPEN same-row
   streaming (that is column-throughput-bound and needs option 1).
3. **Ship the committed win:** the runtime page-policy fix already recovers the
   dominant streaming loss (12.7 -> 112 MB/s, 8.8x, validated on silicon).
   Treat issue-per-clock as a tracked follow-on gated on option 1.

Recommendation: option 3 now (already landed); pursue option 1 as a dedicated
data-path + scheduler co-design task if the residual streaming gap (7.1 -> ~1
cyc/beat) justifies it. Option 2 is a smaller win with limited upside.
