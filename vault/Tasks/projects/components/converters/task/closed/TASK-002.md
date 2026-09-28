# TASK-002: scrub the tests for completeness (converters)

> Migrated 2026-09-27 from `vault/Tasks/projects/components/converters/open.md` as **CONV-008** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** CLOSED 2026-09-27 -- the owner confirmed the scrub was already done. No measurement was taken in this session to support that: the basis is Sean's statement, recorded here rather than dressed up as verification. The sibling closures give it weight -- the same campaign closed in bridge (TASK-003, 2026-09-10), cdc (TASK-001, 2026-09-16), RLB (TASK-006, 2026-09-14) and rapids (TASK-003, 2026-09-27), each with a testqc round named in its closing note. These seven were the stragglers nobody re-statused.
**Status (as filed):** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean. Doing it after coverage would
mean chasing numbers produced by tests nobody has audited.

**Scope:** `projects/components/converters/dv/tests/` -- 16 test files.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units. The brief audits
test collateral against the project's test contract and treats the
CocoTBFramework as reviewed ground truth rather than an audit target. Start
there rather than inventing a method.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test, and the repo has already produced them. The template is
apb5 (2026-09-04): nothing drove `rsp_ready`, so the response skid filled and
never drained, and the TB's completion check returned True on exactly the
state the defect produced. The suite was green BECAUSE the RTL was broken. The
witness added with the fix counted 59 protocol violations across 70 bus
completions on the unfixed design that no prior test had noticed.
**Area-specific:** qc round_41 already found one live example --
`test_uart_axil_bridge.py` passed both before and after the error-reporting
fix, because it only ever saw OKAY responses. It took a new test driving the
slave BFM's `resp_override` to make the defect visible. Look for the same
shape: suites that never exercise the error path they claim to cover.

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

<!-- Moved from vault/Tasks/amba/open.md 2026-09-14: this is a converter
RTL defect and belongs with the converters, not with amba. It sat in the
amba page where nobody reading the converter area would find it. -->
