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
## CDC-002: cdc_4_phase_handshake FAST_PATH acknowledges a transfer the receiver never took

**Priority:** P2 — a real data-loss defect in a shared CDC primitive. Latent in
the only in-tree user, which ties `dst_ready` high, so nothing shipped is
currently wrong.
**Status:** open 2026-09-16. Found by formal the first time the fast path was
ever exercised, under [[CDC-FORMAL-STALE]].

**The defect.** With `FAST_PATH=1`, `D_IDLE` samples `dst_ready` and, on the
synchronized request, sets `dst_valid <= 1` **and** `r_ack_dst <= 1` together,
jumping to `D_WAIT_REQ_CLR`:

```systemverilog
if (FAST_PATH && dst_ready) begin
    dst_valid   <= 1'b1;
    r_ack_dst   <= 1'b1;      // acked before the handshake is observed
    r_dst_state <= D_WAIT_REQ_CLR;
end
```

`dst_ready` was sampled in the PREVIOUS cycle. If it falls before `dst_valid`
rises, `dst_valid && dst_ready` never holds -- the receiver never takes the
beat -- but the ack has already gone back, the source completes, and the data
is silently dropped. `D_WAIT_REQ_CLR` then drives `dst_valid` low, so the beat
is never re-offered.

**Counterexample** (`prove_fast`, step 22): the destination sits in
`D_WAIT_REQ_CLR` with `r_ack_dst=1` while the harness ghost `f_dst_completes`
is still 0, then the source returns ready and accepts a SECOND transfer with
the first never delivered -- `ap_no_lost_transfer` fires.

**It is a defect, not a missing assumption.** `docs/markdown/rtl-cdc/cdc.md`
states a data-stability guarantee for the crossing but places no stability
requirement on `dst_ready`, and ordinary valid/ready lets a receiver drop
ready. The slow path is correct: `D_WAIT_READY` acks only on observing
`dst_ready`.

**Blast radius: nothing shipped is broken.** The only in-tree instantiations
with `FAST_PATH=1` are the two in
`projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/rtl/cdc_counter_domain.sv`
(lines ~482 and ~511), and both drive `.dst_ready (1'b1)`. A constant-high
ready cannot fall, so the window never opens there.

**Two fix shapes, and they are not equivalent:**
1. Make `dst_valid` combinational on the fast branch so the handshake
   completes in the same cycle `dst_ready` is observed. Keeps the one-cycle
   saving, which is the whole point of the parameter, but adds a
   combinational path out of the synchronizer in the destination domain.
2. Ack only on an observed `dst_valid && dst_ready` (i.e. fall back to the
   `D_WAIT_READY` behaviour). Trivially correct, but then `FAST_PATH` saves
   nothing and the parameter should be deleted rather than left as a knob
   that does nothing.

Choosing between them is a design call, which is why this is filed rather
than fixed.

**`formal/cdc/cdc_4_phase_handshake` task `prove_fast` is left RED on
purpose**, so the finding cannot quietly disappear. `prove`, `cover`,
`prove_timeout`, `cover_timeout` and `cover_fast` all pass.

**Test gap worth noting:** `val/cdc/test_cdc_4_phase_handshake.py` sweeps only
clock-period combinations. It sets neither `FAST_PATH` nor `TIMEOUT_CYCLES`,
so no directed test covers either path. That belongs to [[CDC-001]].
