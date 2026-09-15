<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# cdc — Open (accepted, ready to start)

## CDC-001: scrub the tests for completeness (cdc)

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
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module, so a
  test can sit in the file for months and never execute. `test_apb5_master.py`
  did exactly this (2026-09-04) -- the TASK-068 witness added beside the basic
  test ran zero times until the pin was widened. Grep for `testcase=`
  repo-wide; a comma-separated list is the fix when a pin is genuinely wanted.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** [[TASK-078]], [[COMMON-025]], [[MATH-010]] are the same task in
the other three areas.

<!-- Moved from vault/Tasks/amba/open.md 2026-09-14: a CDC formal defect,
filed under amba because that is where CDC used to live before
AMBA-CDC-REORG pulled it out to rtl/cdc. The task never followed. -->
## CDC-FORMAL-STALE — the 4-phase handshake formal proof runs against a pre-rename DUT copy
**Status:** open 2026-07-28 (found by kimi round 10, verified)
**Priority:** P2

`formal/cdc/cdc_handshake/` proves `formal_cdc_handshake.sv`, which compiles
`cdc_handshake_formal.sv` -- a Yosys-compatible copy of the DUT. That copy was
taken before the module became `cdc_4_phase_handshake` and gained parameters:

| | parameters |
|---|---|
| `cdc_handshake_formal.sv` (proved) | `DATA_WIDTH` |
| `rtl/cdc/cdc_4_phase_handshake.sv` (live) | `DATA_WIDTH`, `SYNC_STAGES`, `TIMEOUT_CYCLES`, `FAST_PATH` |

So the proof says nothing about the timeout path (`TIMEOUT_CYCLES > 0` asserting
`src_timeout`) or the fast path (`FAST_PATH=1`, dst accepting when `dst_ready`
is already high) -- the two most recent additions, and the two most likely to
carry a protocol bug.

The doc now scopes its claim
(`docs/markdown/rtl-cdc/cdc.md`, "Verification status"), so nothing currently
overclaims. The work is:

1. Refresh `cdc_handshake_formal.sv` from the live module (it exists because
   Yosys cannot take the `reset_defs.svh` macros -- keep that transformation,
   change nothing else).
2. Extend `formal_cdc_handshake.sv` with properties for the two new parameters.
3. Re-run and confirm the existing properties still pass.

Note the harness is ALSO single-clock/single-reset by construction, which is a
separate and already-documented limitation -- it cannot express the asymmetric
reset hazard. Fixing that is a bigger job and is not this task.

Not a false alarm about the filename: the reviewer flagged
`formal_cdc_handshake.sv` vs `cdc_handshake_formal.sv` as a possible
transposition. Both files exist and both names are correct --
`formal_cdc_handshake.sv` is the harness (`cdc_handshake.sby` has
`prep -top formal_cdc_handshake`) and `cdc_handshake_formal.sv` is the DUT copy.
Confusing, but not wrong.
