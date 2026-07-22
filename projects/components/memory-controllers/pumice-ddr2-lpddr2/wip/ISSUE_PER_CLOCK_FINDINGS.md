# Issue-per-clock (bank-parallel) scheduler — findings + blocker

> Status (2026-07-22): superseded. The bank-parallel issue-per-clock scheduler
> subsequently LANDED (the ordering blocker below was resolved with
> ordering-aware write-buffer backpressure), and the FSM `scheduler.sv` it
> compares against was then retired entirely by the rearchitecture. The
> current command-issue path is `rtl/macro/pumice_mem_cmd_scheduler.sv`
> (see `rtl/PUMICE_MEM_CMD_SCHEDULER_UARCH.md`). Kept as design history.

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

## kb32 ROOT CAUSE (CONFIRMED): w_buf circular overwrite under out-of-order write completion

Ran kb32 with the bank-parallel WIP swapped in + analyzed the test's DFI dumps
(dfi_cmd_q/dfi_wr_data/axi_wr_snoop). Findings:
- 1024 WRA commands issued (correct count); command addresses correct + monotonic
  per bank (bank-interleaved). So the SCHEDULER is fine.
- Burst 254's own write DATA (0x00FE0000) is NEVER driven at DFI; burst 286's data
  is driven TWICE. So the write DATA got mispaired, not the command.
- Writes are strictly serialized atomic ops (0 overlap; 1024 accept/complete) —
  so it is NOT a slot-reuse-during-pull or MAX_CONCURRENT mux race.

DECISIVE experiment: W_BUF_DEPTH 128 -> 4096 makes kb32 PASS. => the bug is the
w_buf circular buffer being overwritten. W_BUF_DEPTH=128 beats = exactly 32 BL4
bursts; bursts 254 and 286 are 32 apart => SAME w_buf region (both mod 32 = 30 ->
beat 120). The AW backpressure uses a SCALAR outstanding count (pushed - freed on
b_complete) which assumes IN-ORDER completion. The bank-parallel scheduler
completes/drains writes OUT OF ORDER (bank-interleaved), so when a younger burst
frees its beats while burst 254 (sharing 286's wrap region) is still un-pulled,
the scalar count under-reports occupancy -> 286's AW is admitted -> 286's W data
overwrites 254's un-pulled region. Matches every symptom: exactly W_BUF_DEPTH/burst
apart, top-only (slow drain keeps ~32 outstanding so the wrap region collides),
bank-parallel-only (the committed FSM retires strictly in-order so the scalar
count is exact). NOT age-wrap, NOT read-ordering, NOT slot-reuse-during-pull,
NOT W-data-outrun (command pushes only after wlast).

FIX (IMPLEMENTED + VERIFIED): ordering-aware w_buf backpressure. wr_cmd_cam gains
a wrap-aware min-age reduction over valid slots and exposes any_outstanding_o +
oldest_wbuf_ptr_o (= the circular TAIL = base of the oldest un-b_completed burst;
the oldest outstanding command is always in the CAM). axi_intake computes a TRUE
circular occupancy = (alloc_head - tail) [WPW-bit sub, W_BUF_DEPTH is pow2 so this
is mod-DEPTH; head==tail with a burst outstanding => FULL] and uses it for the AW
backpressure, falling back to the scalar count only when nothing is outstanding
(exact for in-order/empty). No pointer widening needed. Localized to wr_cmd_cam +
axi_frontend_macro wiring + axi_intake. Committed FSM path is unaffected (it
retires in order, so the tail-based occupancy == the old scalar occupancy).

VERIFIED (bank-parallel scheduler swapped in + this fix, W_BUF_DEPTH back to 128):
kb32 PASS; scheduler FUB 23/23 + command_scheduler_macro 3/3 (26/26); core_macro
109/109. (Sizing w_buf up was only the root-cause confirmation, NOT the fix — it
doesn't scale with N.)

## (superseded) kb32 update 2: age-wrap DISPROVEN; residual is a WRITE-path slot-reuse race

Widened the CAM push-order age to 16 bits + made the counter SATURATE (never
wrap) — implemented across rd/wr_cmd_cam + axi_frontend/pumice_core/command_
scheduler macros + scheduler (AGE_W param). Correct (FUB 23/23, CSM 3/3, core
depth_n1024 pass) but kb32 fails IDENTICALLY (burst 254, wrote f(254) read
f(286)). So the age WRAP was NOT the root cause — DISPROVEN. Reverted the widen
to keep the committed FSM shipping green (it forced widening the FSM too for no
benefit); the read-ordering WIP stays 8-bit to match the macros.

DEFINITIVE localization: it's a WRITE-path slot-reuse race. 254 mod 16 == 286
mod 16 == 14 -> burst 254 and burst 286 use the SAME write CAM slot; burst 286's
data lands at burst 254's DRAM address (memory[addr_254] = f(286)). Reads AND
writes are both verified issue-in-order (probes), the aligner emits in issue
order (no age compare), and widening the age changes nothing -> the bug is
w_buf slot free->reuse vs write-data drain in the data path (wr_beat_sequencer /
axi_intake / w_buf), exposed by the bank-parallel scheduler's write pacing (the
old FSM's slower one-op-at-a-time cadence never reaches the reuse window). NEXT:
gate w_buf slot reuse on the previous write's data fully draining (b_complete),
or add a per-slot "data valid" interlock — a data-path fix, not scheduler.

## kb32 update 1: read reorder FIXED; (earlier age-wrap hypothesis, now disproven)

Added a self-checking probe (RD column commands must issue in monotonic age
order) — it caught the reorder and now verifies the fix. Root cause of the
reorder: at N=1024 the rd_cmd_cam's 8-bit age counter WRAPS (255->0) ~every 256
reads; same-id reads spanning the wrap sit on DIFFERENT banks, so bank-parallel
issue let a younger read (age 0) beat an older one (age 241) -> the strictly
in-issue-order read return path (rd_cl_aligner + axi_intake R-emit) mis-paired
data with requests.

FIX (in wip, verified reorders=0): reads issue strictly in AR (age) order —
one read op in flight at a time (`w_any_read_if` gates read assignment) and the
read tournament leaf drops the bank-busy mask so the GLOBALLY oldest read is
always surfaced (a younger read on a free bank can't jump an older read on a
busy bank). Writes stay fully bank-parallel (each carries its own address).
Probe now reports **0 reorders**.

BUT kb32 still fails (burst 254, then 511 after also serializing writes) —
always JUST BEFORE an age-wrap multiple (256, 512). Reads AND writes are both
verified in-order, and the aligner emits in issue order (no age compare in the
data path), so this is NOT scheduler ordering. It is a DATA-PATH interaction of
the 8-bit age wrap with real DFI read latency (top-level only — core-macro
N=1024 passes because its near-zero-latency model never builds the outstanding
depth that exposes it). Symptom: `wrote f(254) read f(286)` — burst 286's data
at burst 254's slot (286-254 = 32 = 2xCAM_DEPTH -> slot-reuse). The old FSM's
slower one-op-at-a-time pacing never reaches this boundary condition.

Next: waveform-debug the read path (rd_cl_aligner per-op DFI capture / staging)
+ write w_buf slot free->reuse at the age-wrap + real-latency boundary; or widen
the CAM age so it doesn't wrap over the outstanding-window lifetime (invasive:
AGEW in rd_cmd_cam/wr_cmd_cam + all scheduler age paths). The read-ordering fix
is correct regardless and stays in the WIP.

## RESOLVED: the primary bug was refresh interrupting an in-flight op

The "nondeterministic slot-reuse race" below was mis-diagnosed. Waveform tracing
of `id_fixed_7_n64` (disable refresh via a huge t_refi → it PASSES) pinned the
real cause: the bank-parallel issuer GRANTED refresh while a column op was mid
ACT→RDWR, interrupting its data transfer (the old single-op FSM only granted
refresh in S_IDLE, between ops). Fix (in wip/scheduler_bankparallel_wip.sv):
**quiesce before refresh/MRS/pdn** — `w_do_assign` is gated by `!w_quiesce_req`
so no NEW op launches while such a request is pending, and the injection is
granted only when all banks are idle (`!w_any_pv`); in-flight ops drain first.

Result with the quiesce fix (all clean, refresh enabled):
- scheduler FUB: **23/23**   - command_scheduler_macro: **3/3**
- pumice_core_macro: **109/109** (full matrix)
- pumice_top: **88/89**

REMAINING: `pumice_top engine_mirror[kb32]` (N=1024, FIXED-id, TOP level with
real DFI PHY timing). The OLD FSM passes it; the bank-parallel version fails with
a same-id READ reorder — at N=1024 the address range spans many banks, and the
read return path (rd_cl_aligner + axi_intake R-emit) is strictly in-issue-order
while the host matches the Nth R burst to the Nth AR. A younger same-id read
whose bank readies first is issued ahead of an older one → mis-paired data.
(core-macro same-id tests stay single-bank at their N, so they don't expose it.)
Attempts to enforce read AR-order in the scheduler (one-read-in-flight; oldest-
read-only leaf; an age-based issued-guard) moved the failure later (burst
241→254) but a) did not fully close it and b) broke FUB `random_soak` (the
age-contiguity assumption / read serialization is too fragile). A correct fix
needs a dedicated, carefully-verified AR-order read-issue mechanism (e.g. a
per-id next-expected-age pointer sourced from the rd_cmd_cam's real age
semantics) checked against BOTH `random_soak` and `kb32`. Until then the
bank-parallel scheduler is NOT instantiated; committed scheduler.sv (old FSM +
runtime policy) ships and keeps kb32 green.

## (Earlier mis-diagnosis) slot-reuse RACE

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
