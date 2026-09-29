# TASK-002: scrub the tests for completeness (misc)

> Migrated 2026-09-27 from `vault/Tasks/projects/components/utility-ip/misc/open.md` as **MISC-002** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** CLOSED 2026-09-27 -- the owner confirmed the scrub was already done. No measurement was taken in this session to support that: the basis is Sean's statement, recorded here rather than dressed up as verification. The sibling closures give it weight -- the same campaign closed in bridge (TASK-003, 2026-09-10), cdc (TASK-001, 2026-09-16), RLB (TASK-006, 2026-09-14) and rapids (TASK-003, 2026-09-27), each with a testqc round named in its closing note. These seven were the stragglers nobody re-statused.
**Status (as filed):** open 2026-09-04. The misc slice of the repo-wide test scrub that
was meant to ride along with the kimi review packets and got dropped.

**Sequencing.** A FOCUSED pass, after qc/humanize is finished everywhere and
BEFORE coverage and formal are driven clean.

**Scope:** `projects/components/utility-ip/misc/dv/tests/` -- 4 test files covering the
AXI4 interface observers and the tally/slave-monitor register blocks.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units.

**Area-specific:** the observers are measurement-only blocks, which is the
hardest thing to test honestly -- a monitor that reports nothing looks
identical to a bus with nothing on it. Check that each test proves the
observer SAW something, not merely that it did not fault. The area also
carries the `axi4_intf_observer` work that a stream channel-3 hang was traced
to (the observer's `block_ready` replaying 49 ARs as 367), so its tests have a
history of passing while the block misbehaved.

**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names.
- No test asserts a condition the bug itself satisfies.
- Inputs the DUT needs are actually driven.
- gate/func/full levels mean something distinct, not three names for one run.
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module.
  `test_apb5_master.py` did exactly this (2026-09-04).
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL.

**Related:** [[TASK-078]], [[COMMON-025]], [[MATH-010]], [[CDC-001]],
[[BRIDGE-007]], [[PUMICE-018]], [[CONV-008]], [[APBX-007]], [[RLB-006]],
[[TASK-079]], [[TASK-080]] are the same task in the other areas.
