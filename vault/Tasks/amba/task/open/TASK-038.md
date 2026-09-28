# TASK-038: scrub the tests for completeness (amba)

> Migrated 2026-09-27 from `vault/Tasks/amba/open.md` as **TASK-078** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way.

**Sequencing.** This is a FOCUSED pass, run after qc/humanize is finished
everywhere, and BEFORE coverage and formal are driven clean. Doing it after
coverage would mean chasing numbers produced by tests nobody has audited.

**Scope:** `val/amba/` -- AXI4/AXI5, APB4/APB5, AXI-Stream, gaxi, the monitor subsystem and monbus.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units. The brief audits
test collateral against the project's test contract, with the CocoTBFramework
treated as reviewed ground truth rather than an audit target. Start there
rather than inventing a method.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test, and this area has already produced them:

- `apb5_master` (2026-09-04): the suite was green *because* the RTL was
  broken. Nothing drove `rsp_ready`, so the response skid filled after
  RSP_DEPTH transfers and never drained; the master held PSEL/PENABLE past
  PREADY, and `wait_for_transaction()` scored that state a pass. Fixing the
  RTL made the old test time out. The witness added with the fix counted 59
  protocol violations across 70 bus completions on the unfixed design --
  none of which any prior test noticed.
- `apb5_slave` had no coverage at all for the orphan-response case that
  `apb4_slave` was hardened against after a real Nexys A7 misalignment.
- `test_apb5_master.py` pinned `testcase=` to a single cocotb test, so a
  second test added to the file silently never ran. Worth grepping for
  repo-wide: any pinned `testcase=` hides every other test in its module.

**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names (the
  `bin/check_test_dut_family.py` gate catches the family-level version of
  this; it does not catch a test that drives the right DUT trivially).
- No test asserts a condition the bug itself satisfies. The apb5 case is the
  template: `wait_for_transaction()` returned True on `PENABLE && PREADY`,
  which is exactly the state the defect produced.
- Inputs the DUT needs are actually driven. `rsp_ready` was never assigned in
  the apb5 master TB, so the response path was never exercised.
- gate/func/full levels mean something distinct, not three names for one run.
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module, so a
  test can sit in the file for months and never execute. `test_apb5_master.py`
  did exactly this (2026-09-04) -- the TASK-068 witness added beside the basic
  test ran zero times until the pin was widened. Grep for `testcase=`
  repo-wide; a comma-separated list is the fix when a pin is genuinely wanted.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** amba TASK-077 (CLOSED 2026-09-25, now in `closed.md`)
documented the doc-side equivalent (examples that
name ports which do not exist). The test-side is this task.

---
