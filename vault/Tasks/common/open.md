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
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module, so a
  test can sit in the file for months and never execute. `test_apb5_master.py`
  did exactly this (2026-09-04) -- the TASK-068 witness added beside the basic
  test ran zero times until the pin was widened. Grep for `testcase=`
  repo-wide; a comma-separated list is the fix when a pin is genuinely wanted.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** [[TASK-077]] documents the doc-side equivalent (examples that
name ports which do not exist). The test-side is this task.

### COMMON-026: FIFO-family reset bodies hardcoded active-low - FIXED

**Status:** fixed 2026-09-10 (Sean authorized the shared-RTL edit: "they are
innocent and make RLB coding easier"). Raised by the smbus #58 round-6 review.

`reset_defs.svh` makes reset polarity a compile-time property: the
`ALWAYS_FF_RST` sensitivity follows the define, and `RST_ASSERTED()` is how a
body is meant to test the level. Ten files in the FIFO family tested it by
hand instead, in two shapes: a body of `if (!rst_n)` inside the macro (18
sites), and a raw `always_ff @(posedge clk, negedge rst_n)` that bypassed the
macro entirely (3 sites, in `fifo_control.sv` and `counter_bingray.sv`).
Under `-DRESET_ACTIVE_HIGH` the storage then sat in reset forever while the
wrapper counters kept counting, so a FIFO reported empty with data in it.

Measured before and after on a standalone `fifo_sync`, three bytes written:

| build | before | after |
|---|---|---|
| default (active-low) | `empty=0 head=0xA0` | `empty=0 head=0xA0` |
| `-DRESET_ACTIVE_HIGH` | `empty=1 head=0xA2` | `empty=0 head=0xA0` |

Files: `rtl/common/{fifo_control,fifo_sync,counter_bin,counter_bin_load}.sv`,
`rtl/cdc/{fifo_async,gaxi_fifo_async,counter_bingray,counter_johnson}.sv`,
`rtl/amba/gaxi/{gaxi_fifo_sync,gaxi_drop_fifo_sync}.sv`. `counter_bingray.sv`
also gained the `reset_defs.svh` include it never had.

**Still open, same defect class, NOT in this change:** twelve non-FIFO files
carry the same hand-written `if (!rst_n)` inside the macro - the apb4/apb5
and axis5 clock-gate wrappers, `axil5_opt_slave`, `amba_clock_gate_ctrl`,
`clock_divider`, `dataint_checksum`, and the raw block in
`clock_gate_ctrl.sv`. They are a separate family with a separate regression;
see [[COMMON-027]]. The sibling in the RLB wrappers is [[RLB-012]].

### COMMON-027: non-FIFO reset bodies hardcoded active-low

**Priority:** P3 today (no build sets `RESET_ACTIVE_HIGH`).
**Status:** open 2026-09-10. Split out of [[COMMON-026]], which fixed the
FIFO family under the same defect class.

Twelve files test the reset level by hand inside `ALWAYS_FF_RST` (`if (!x)`
rather than `` `RST_ASSERTED(x) ``), or bypass the macro with a raw
`always_ff`: `rtl/amba/apb4/{apb4_master_cg,apb4_slave_cg}.sv`,
`rtl/amba/apb5/{apb5_master_cg,apb5_slave_cg,apb5_slave_cdc_cg}.sv`,
`rtl/amba/axis5/{axis5_master_cg,axis5_slave_cg}.sv`,
`rtl/amba/axil5/test-modules/axil5_opt_slave.sv`,
`rtl/amba/shared/amba_clock_gate_ctrl.sv`,
`rtl/common/{clock_divider,dataint_checksum}.sv`, and the raw block in
`rtl/common/clock_gate_ctrl.sv`. The mechanical fix is the same one
COMMON-026 used; the reason it is separate is the regression, which is the
amba and common areas rather than the FIFO consumers.

