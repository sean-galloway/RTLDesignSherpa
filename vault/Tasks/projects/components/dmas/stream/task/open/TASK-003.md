# TASK-003: scrub the tests for completeness (stream)
> **Was `TASK-079` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**ID note:** this area draws from the shared `TASK-nnn` sequence, whose
counter lives in [amba/INDEX.md](../../../../../../amba/INDEX.md). It is not a
per-area namespace -- take the number from there and bump it.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean.

**Scope:** `projects/components/dmas/stream/dv/tests/` -- 17 test files across fub/macro/top.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test. The template is apb5 (2026-09-04): nothing drove
`rsp_ready`, so the response skid filled and never drained, and the TB's
completion check returned True on exactly the state the defect produced. The
suite was green BECAUSE the RTL was broken.

**Area-specific:** stream has already produced two of the repo's clearest
"the test was wrong, not the RTL" cases -- the sram_controller alloc failures
that were the TB sampling `space_free` before its register pipeline settled,
and the scheduler write-timeout that a TB signal poke could not reach because
the value is register-driven on the top. Both are the inverse of the apb5 case
and both belong in the scrub's findings taxonomy.
**A concrete find already in hand (2026-09-24, from TASK-002).**
`dv/tests/top/test_stream_top_mon_cfg.py` checks `rb == 0xDEADBEEF` and reports
"the register is unreachable". Nothing in that DUT's closure can drive
0xDEADBEEF -- it appears only as an `LFSR_SEED` in `rtl/amba/shared` and as
`axi4_subtractive_slave`'s READ_FILL, and `read_apb_register` returns
`packet.fields.get('prdata', 0)`, defaulting to 0. So the branch is dead: an
assertion that cannot fire, which is exactly this task's "no test asserts a
condition the bug itself satisfies" clause in its inverse form.

`test_stream_top_regs.py` had the SAME defect and is **already fixed** -- do not
re-do it. It was worse there: the sentinel sat in that file's monitors-absent
`xfail`, which was TASK-002's own regression gate, so the gate could not observe
its fix and stayed XFAIL after it landed. Fixed under TASK-002 by adding
`StreamCoreTB.last_rsp_pslverr` and moving the predicates onto the real APB
error response. `test_stream_top_mon_cfg.py` is the remaining one.

**A second find (2026-09-24, measured while closing TASK-002).** Every test in
`dv/tests/top/` sets `COCOTB_RESULTS_FILE` in `extra_env`, and **no
`results_*.xml` is ever written** -- zero in `logs/`, zero under the stream
area, and zero repo-wide (439 test files set the variable). The `.log` file is
the only real record.

Scoped honestly: this is INERT CONFIG, not a broken pipeline. Both consumers
handle absence deliberately -- `bin/aggregate_test_results.py:648` prints "No
XML results found" and names three alternatives (`--run`, `--scan-dir`,
`--list`), and `bin/cov_utils/functional_coverage_tracker.py:110` takes its
directory as a parameter and returns `{}` when empty. So nothing is silently
losing data; 439 files just carry a setting that does nothing. Worth settling
whether the variable is inert with this cocotb-test version and should be
dropped, or should work and something discards it -- a suite should not
configure an artifact it never produces.

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
