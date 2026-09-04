# RLB — Open (accepted, not started)

---

## RLB-003 — Fix remaining MAS register documentation (4 blocks)
**Status:** open 2026-07-22

The four `documentation` issues whose problems are targeted (wrong reset values,
undocumented bits, wrong port lists) rather than wholesale-wrong maps. Same
method as RLB-002: rewrite the MAS register chapter against the RTL decode,
independently re-verify offsets with `rlb-doc-review` (or scratchpad copy of)
`verify_regmap.sh` before committing, commit scoped to each block's docs,
reference the issue.

- **gpio** — issue #43. Undocumented GPIO_CONTROL[1] INT_ENABLE (per MAS, irq
  can never assert); 4 omitted registers (RAW_INT 0x24, OUTPUT_SET/CLR/TGL
  0x28/2C/30); wrong reset values on CONTROL/INT_POLARITY.
- **hpet** — issue #45. HPET_ID vendor/revision hardcoded (params dead) + field
  errors. (NOTE: the review's hpet criticals C1-C3 are RTL bugs → RLB-004.)
- **ioapic** — issue #47. Register-map/field corrections (mostly High; the C1
  double-delivery is an RTL bug → RLB-004).
- **pit_8254** — issue #51. PIT_STATUS reset value wrong (doc 0x00303030,
  actual 0x00404040); wrong top-level port list, wrong PADDR width (12b not
  32b), undocumented PPROT, wrong reset port name (pit_resetn not pit_rst_n);
  SLVERR-on-unmapped behavior doesn't exist (errors tied off, 0x20 aliasing).

## RLB-005 — Clean up rtc wavedrom README third register-map copy
**Status:** open 2026-07-22

`docs/rtc_mas/assets/wavedrom/timing/README.md` still holds a THIRD,
contradictory register map (TIME_LO@0x00, REG_A/B/C, UIP/rate-select) that the
rtc fix (RLB-002) left as out-of-scope. Correct it to the real map or regenerate
the wavedrom assets. (pic_8259 and pm_acpi wavedrom READMEs were already fixed in
their commits.)

### RLB-006: scrub the tests for completeness (retro legacy blocks)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

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
