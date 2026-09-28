# TASK-006: scrub the tests for completeness (retro legacy blocks)

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-006** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** closed 2026-09-14. DONE for retro_legacy_blocks 2026-09-11. Raised by Sean
2026-09-04: test scrubbing was meant to be part of the kimi review packets and
got dropped along the way. This entry covered the RLB suites; the same task in
the rtl/ areas is [[TASK-078]], [[COMMON-025]], [[MATH-010]], [[CDC-001]].

**What the pass found, criterion by criterion.** Each was checked
MECHANICALLY where a machine could check it, because the alternative is a
reviewer's impression:

1. *Every test exercises the DUT it names.* Clean. All nine wrappers build the
   `apb4_<block>` matching their filename.
2. *No test asserts a condition the bug itself satisfies.* ONE FINDING, fixed.
   `test_gh58_r4_10_tx_fifo_pstrb` imported the framework's `APBPacket` behind
   a try/except that returned **True** when the import failed -- a test that
   passes on the failure of its own precondition, so a framework rename would
   have turned it green while it drove nothing. The import is unconditional
   now.
3. *Inputs the DUT needs are actually driven.* Clean: 120 input ports across
   the nine tops, every one driven. The checker that proved it first reported
   `hpet_clk` and `rtc_clk` as undriven because it only recognised `.value =`
   and not `Clock(self.dut.x)`; a checker with false positives is one nobody
   reads, so it was fixed before its output was believed.
4. *gate/func/full mean something distinct.* THE BIG ONE, fixed. MEASURED
   BEFORE: pm_acpi's gate, func and full cells each logged
   `Starting FULL PM_ACPI` and each ran the identical 57 tests. All nine
   blocks were in that state, and hpet was worse -- every one of its six cells
   was pinned at `'full'`, so it had never run a gate or a func depth at all.
   Cause is TOOL-016: `cocotb_test.set_env` copies `os.environ` over
   `extra_env`, so the conftest `REG_LEVEL -> TEST_LEVEL` stamp beat every
   per-cell value. Converted both halves in one commit per the bridge's worked
   example -- every wrapper now parametrizes on `reg_level_grid()` and passes
   `level_env()`, and the stamp is gone. The grid moves now: GATE 21 cells,
   FUNC 41, FULL 61, where all three used to collect 49 and run them all deep.
5. *Every test offers gate/func/full.* ONE EXCEPTION, fixed 2026-09-11 after
   Sean restated the requirement: `test_rtc_gh56_timeout_sweep` collected
   exactly one cell at GATE, FUNC and FULL alike. It is levelled now, and
   what the levels MEAN there is deliberately unlike the rest of the area --
   every other test grades by how many suites run, this build exists for one
   narrow thing so it grades by how hard the watchdog is pushed: gate is the
   headline case, func adds the queued-commit orderings, full adds the
   same-edge races that sweep eight points apiece. The contract is that all
   three exist and differ, not that they differ the same way everywhere; a
   component's levels will not mean what a generic fub's do. Verified by
   collecting all three grids: every test is now 1/2/3 or 2/4/6, none flat.
6. *No `run()` pins `testcase=`.* Two pins in `test_apb4_rtc.py`, both
   JUSTIFIED and both covered: the module holds two `@cocotb.test()`
   functions that need different `COMMIT_TIMEOUT_CYCLES` builds, and each
   pytest cell pins its own. Checked by AST that no cocotb test in any module
   is unreachable. Nothing hidden.
7. *A fix landed with a test has its mutation check recorded.* Reported
   PARTIAL; **RETRACTED 2026-09-14 -- the gap does not exist.** ioapic,
   pit_8254 and rtc carried it in the test file; pm_acpi carries it in the
   GH54 suite; gpio and hpet had it only in commit messages and now carry it
   in the test files.

   This entry then said "**smbus, uart_16550 and pic_8259 have NO record that
   their defect-regression tests were ever seen RED**". That is FALSE, and it
   was checked before being retracted. All three carry one, two of them
   prominently:
   - pic_8259: `pic_8259_tests_medium.py:30`, "this suite was authored RED
     (2026-09-09) against the pre-fix RTL", plus per-test "expected RED
     against current RTL" notes in `test_apb4_pic_8259.py`.
   - smbus: `test_apb4_smbus.py:109`, "GH#58 RED regression tests -- written
     FIRST, against the unfixed" RTL, and the RED result named as the
     deliverable finding.
   - uart_16550: `uart_16550_tests_medium.py:524` and `:1128`, the GH60 and
     GH60-R2 batches both described as RED tests against the pre-fix RTL.

   **How the original claim went wrong is the lesson.** It was produced by a
   search that missed the phrasing those files actually use ("authored RED
   against the pre-fix RTL", "written FIRST against the unfixed"). The first
   re-check repeated the mistake with a pattern that ALSO returned zero for
   ioapic -- a known-present case -- which is what exposed it. A checker that
   returns zero for a case you know is present is measuring nothing; test the
   instrument against a known positive before believing its negatives. Nobody
   should revert a fix on the strength of the retracted claim.

**Still open elsewhere:** the same scrub for the rtl/ areas, and the
`bin/review/run_batch.py testqc` round, which has never been run for any
projects/components area (BRIDGE-007). This pass applied the brief's criteria
directly rather than routing them through the external reviewer; a testqc
round would still add value on the parts a machine cannot check.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean. Doing it after coverage would
mean chasing numbers produced by tests nobody has audited.

**Scope:** `projects/components/retro_legacy_blocks/dv/tests/` -- 9 test files covering the 8259/8254/16550/SMBus/PM-ACPI/RTC cores.

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
**Area-specific:** several cores here have not been touched since 2025-11 and
their `_core` modules are undocumented, so the tests are currently the only
statement of intended behaviour. That makes an unaudited test in this area
more load-bearing than elsewhere, not less.

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
