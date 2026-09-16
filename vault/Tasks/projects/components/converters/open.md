<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# converters — Open (accepted, not started)

## CONV-008: scrub the tests for completeness (converters)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
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
## CONV-010: dwidth converter split-fold assumes in-order B across IDs

*Renumbered from CONV-001 on 2026-09-14. It was filed in `vault/Tasks/amba/`,
where CONV-001 was free; moving it to the area it belongs to put it against the
converters' own CONV-001 (a resolved dnsize LAST fault). The area is the ID
namespace, so the clash only appeared once the task was in the right place.*

**Priority:** P3 — latent, needs an interleaving downstream AND a master using
multiple write IDs through the converter at once. No shipped integration in
this repo does both today.
**Status:** open 2026-09-01. Raised as a SUSPECTED finding in qc round_31,
verified against the RTL, documented in
`docs/markdown/rtl-amba/axi4/axi4_dwidth_converter.md`. Filed rather than fixed
because it changes a converter used by pumice's host gearing
([[project_pumice_axi_width_gearing]]) — scope call belongs to Sean.

**What the RTL does.** `axi4_dwidth_converter_wr.sv` splits one oversized slave
burst into several master bursts and records each in a single FIFO:

    logic [9:0]         splitq_mem [SPLITQ_DEPTH];
    logic [SPLITQ_AW:0] splitq_wptr, splitq_rptr_w, splitq_rptr_b;
    assign split_b_final = splitq_mem[splitq_rptr_b[SPLITQ_AW-1:0]][9];

The B fold pops one entry per downstream response and forwards a B to the slave
only on the record marked final.

**Why it is only sometimes correct.** All pieces of one split burst carry the
AWID of the burst they came from, and AXI4 guarantees same-ID B responses come
back in order — so within one ID the FIFO fold is exact. Across IDs AXI4 places
no such ordering requirement. If two slave bursts with different IDs are both
split and the downstream interleaves their responses, the FIFO cannot tell them
apart and decrements the wrong record: one burst's B is released early, the
other's never completes.

**Fix shape.** Make the fold ID-aware — a small CAM keyed by AWID, or one split
counter per outstanding ID — rather than a single ordered FIFO. The read side
(`axi4_dwidth_converter_rd.sv`) should be checked for the same pattern.

**Test that would catch it.** Two concurrent split write bursts on distinct
AWIDs against a downstream model that returns B out of order; assert each slave
B arrives exactly once, after its own last master burst.
