<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Open (accepted, ready to start)

### COMMON-025: scrub the tests for completeness (common)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way.

**Sequencing.** This is a FOCUSED pass, run after qc/humanize is finished
everywhere, and BEFORE coverage and formal are driven clean. Doing it after
coverage would mean chasing numbers produced by tests nobody has audited.

**Scope:** `val/common/` -- the ~57 reusable building blocks.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units. The brief audits
test collateral against the project's test contract, with the CocoTBFramework
treated as reviewed ground truth rather than an audit target. Start there
rather than inventing a method.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test, and this area has already produced them:

- The area's own qc rounds (round_38/39) found my "no test coverage" claims
  were wrong for 5 of 7 modules -- the tests existed but built their own
  wrappers, so a name-based search missed them. The inverse error is the one
  this task must catch: a test that exists, is found, and proves nothing.
- `apb4_master_cg` had no filelist at all, which is why it had no test. A
  completeness scrub has to check the filelist -> test chain, not just the
  test directory listing.

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
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** [[TASK-077]] documents the doc-side equivalent (examples that
name ports which do not exist). The test-side is this task.
