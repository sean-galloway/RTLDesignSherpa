<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# cdc — Open (accepted, ready to start)

### CDC-001: scrub the tests for completeness (cdc)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way.

**Sequencing.** This is a FOCUSED pass, run after qc/humanize is finished
everywhere, and BEFORE coverage and formal are driven clean. Doing it after
coverage would mean chasing numbers produced by tests nobody has audited.

**Scope:** `val/cdc/` -- `bin2gray`, `gray2bin`, the async FIFOs and the
pointer-synchroniser family.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units. The brief audits
test collateral against the project's test contract, with the CocoTBFramework
treated as reviewed ground truth rather than an audit target. Start there
rather than inventing a method.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test, and the repo has already produced them:

- `bin2gray` and `gray2bin` were invisible to the doc/port auditor for weeks
  because their ports are declared `input wire` rather than `logic` -- the
  tooling reported zero ports and scored them fully documented. Tooling that
  silently sees nothing is the same class of failure a test scrub looks for.
- In `amba` the same week, the apb5 master suite was green *because* the RTL
  was broken: nothing drove `rsp_ready`, and the TB's completion check
  returned True on exactly the state the defect produced. See [[TASK-078]].
- This area is small enough that a complete scrub is cheap, and it feeds the
  async-FIFO and pointer-encoding work the rest of the repo depends on.

**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names.
- No test asserts a condition the bug itself satisfies.
- Inputs the DUT needs are actually driven.
- gate/func/full levels mean something distinct, not three names for one run.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** [[TASK-078]], [[COMMON-025]], [[MATH-010]] are the same task in
the other three areas.
