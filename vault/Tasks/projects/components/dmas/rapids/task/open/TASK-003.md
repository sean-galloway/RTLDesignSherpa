# TASK-003: scrub the tests for completeness (rapids)
> **Was `TASK-080` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**ID note:** this area draws from the shared `TASK-nnn` sequence, whose
counter lives in [amba/INDEX.md](../../../../../../amba/INDEX.md). It is not a
per-area namespace -- take the number from there and bump it.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean.

**Scope:** `projects/components/dmas/rapids/dv/tests/` -- 17 test files.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test. The template is apb5 (2026-09-04): nothing drove
`rsp_ready`, so the response skid filled and never drained, and the TB's
completion check returned True on exactly the state the defect produced. The
suite was green BECAUSE the RTL was broken.

**Area-specific:** rapids has not been functional for roughly two months and
work resumes only after qc/humanize, the flat-flow migration and formal are
done (Sean, 2026-09-03). Do NOT start this scrub before the area is live
again -- auditing tests against RTL that is about to change is wasted effort.
This block exists so the requirement is recorded, not so it gets picked up
early.
**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names.
- No test asserts a condition the bug itself satisfies.
- Inputs the DUT needs are actually driven.
- gate/func/full levels mean something distinct, not three names for one run.
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module, so a
  test can sit in the file for months and never execute. `test_apb5_master.py`
  did exactly this (2026-09-04) -- a witness added beside the basic test ran
  zero times until the pin was widened. A comma-separated list is the fix when
  a pin is genuinely wanted.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** [[TASK-078]], [[COMMON-025]], [[MATH-010]], [[CDC-001]] are the
same task in the rtl/ areas.

---

**Progress 2026-09-27 -- the scrub ran.** Bundles for all five rapids test areas built with
`bin/review/build_test_review_bundle.py`, ten units reviewed in `testqc` mode against
`TEST_REVIEWER_BRIEF.md` (local proxy, kimi-k2; results kept in the session scratchpad), every
finding triaged and acted on in-tree:
- Seeds: 14 runners pinned `SEED=12345` and overrode the environment; all now
  `os.environ.get('SEED', random)`. Level mechanisms: REG_LEVEL grids and TEST_LEVEL depth
  added to ctrlrd/ctrlwr, alloc/drain, descriptor engine, scheduler (+timeout), monbus group,
  top runners; pytest names embed the module in alloc/drain/monbus/timeout.
- Checks that could not fail, now real: ctrlrd/ctrlwr null-address (AR/AW count + memory),
  ctrlrd reset idle, ctrlwr misaligned (entry point added), descriptor engine invalid /
  out-of-range / monitor packet (decoded), scheduler IRQ (RAPIDS_EVENT_IRQ) and FSM states,
  latency bridge data path (behind a real REGISTERED FIFO wrapper -- the BFM-driven test had
  read zeros), snk/src SRAM controllers (drain sampled before the pop; payload compared),
  snk/src AXIS data paths (memory compared beat by beat; per-descriptor counter deltas),
  scheduler group config/monbus (background capture), array monbus aggregation, monbus group
  (arbiter/input framework monitors, master-write AW/W accounting, filtering observed, error
  records rebuilt and compared; the TB had never reset its AXIL slave, used a 32-bit read BFM
  on a 64-bit drain and sent ARB-protocol packets the DUT has no config for),
  rapids_core/top (busy-then-idle wait; over-delivery fails).
- Two RTL defects surfaced on the way (rapids BUG-004/005).
**Still open from the review:** hand-rolled AXI responders in ctrlrd/ctrlwr (framework gap on
narrow reads, see reference note), hand-rolled AXIS egress monitor / AXIL capture responder in
`rapids_beats_top_tb` and `rapids_core_beats_tb`, and `src_data_path_axis_test_beats_tb`'s
end-to-end data-integrity compare against `expected_data`. Those are refactors, not gaps in
the contract's checkable clauses; scheduled next.

**2026-09-27, first clean full regression after the scrub:** fub 48/48, macro_beats 249/249;
fub_beats 27 and macro 2 failures, top_beats source/perf_ch failures. All root-caused:
descriptor-engine `descriptor_error` is a two-cycle pulse that a blind 100-cycle wait
missed (background watcher now, started before the kick); the out-of-range step was RIGHT
and the RTL wrong -- rapids BUG-006 (kicked address never range-checked), fixed;
latency-bridge streaming guard was a fixed 2000 cycles for 200 slow-producer beats (scales
with beats now); monbus basic_flow counted the arbiter 60 cycles after the last input
while 5 packets still sat in the input skids (waits for the arbiter to catch up); the top
source path called the busy-then-idle wait AFTER its beat-capture wait, so the half was
already idle again (wait moved to right after the kick). Rerun is recorded below.
