<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# converters — Open (accepted, not started)

---

## CONV-001 — axi_data_dnsize burst-tracking LAST: early LAST on TRACK_BURSTS
**Status:** RESOLVED as a test fault 2026-08-23 — mechanism proven correct; residual flake folded into [[CONV-003]]

**Resolution.** The TRACK_BURSTS LAST mechanism is correct.
`test_burst_len_drives_last` frames a burst and holds `wide_last` LOW, so
the counter is the only thing that can assert LAST -- it lands exactly on
`burst_len`, on all 16 configurations including DUAL. That test is asserted
and green.

Everything that looked like an RTL defect was test-side, in three layers:
the signal mapping (LAST never bound, so it read False always), the framing
units (wide beats where the RTL counts narrow), and fixed waits that let a
previous burst's tail be read as the next burst's beat 0. All fixed.

`test_burst_tracking` itself remains intermittently red on DUAL and is left
unasserted -- but the failure it shows is a DUAL-buffer symptom shared with
CONV-003, not a burst-tracking one. Tracking it there.

**Superseded detail below.**

**Status:** open 2026-08-22; narrowed 2026-08-23
**Priority:** P1 — either a broken feature or a broken test, and neither is known

**Update 2026-08-23.** Two of the three suspects are eliminated. The signal
mapping was broken (`field_last_sig` never resolved, so LAST read as 0
regardless of what the RTL did) and the framing units were wrong (wide beats
where the RTL counts narrow). Both are fixed. With LAST actually observable,
the symptom changed from "LAST never asserts" to **"LAST asserts early"** --
`Burst 2, beat 3: expected False, got True`, beat 3 being the end of the
first WIDE beat at ratio 4. That is a real behavioural question about the
counter path, not an artefact. Everything below still applies.

`test_axi_data_dnsize.py` calls the scenario without checking it:

```python
await tb.test_burst_tracking(num_bursts=15)     # return value discarded
```

`test_burst_tracking` returns False on a LAST mismatch. Nothing reads it, so
the scenario has been reporting a failure into the void. All 16 configs show
green.

**Assert it and 6 configs go red** — every `TRACK_BURSTS=1` parametrization.

### What is established

`burst_len` is **narrow beats − 1**, not wide. In TRACK_BURSTS mode
`narrow_last` is driven *only* by the counter — `wide_last` plays no part:

```systemverilog
assign narrow_last = r_wide_buffered && r_burst_active &&
                     (r_slave_beat_count + 1'b1 >= r_slave_total_beats);
```

and `r_slave_beat_count` increments on every narrow beat sent, with
`r_slave_total_beats = burst_len + 1`. The scenario frames its bursts in
*wide* beats (`start_burst(burst_len_beats - 1)`), which is a factor of
`WIDTH_RATIO` short, so LAST should fire early.

### What is NOT established

Correcting the framing to narrow beats does not fix it. With
`burst_len = 7` for an 8-narrow-beat burst, LAST is still absent on beat 7 —
the beat where `(7 + 1) >= 8` should assert it. So there is a second effect
beyond the units error, and it is unresolved. Candidates: `r_burst_active`
clearing early, or the scenario's `wide_last` interacting with the counter
path.

### Why the suite is still green in the tree

Asserting the result turns 6 configs red without diagnosing anything. The
assert is left off with a pointer to this task. **The silent discard is
itself the defect** — fix that as part of this task, not separately.

### Related, already done

The throughput measurement added alongside this
(`measure_throughput`, `measure_burst_throughput`) works and is asserted.
Simple mode sustains 0.992 beats/cycle; TRACK_BURSTS ~0.914–0.941 with
narrow-beat framing, consistent with one bubble per burst boundary.

**Work:**
- [ ] Determine whether the TRACK_BURSTS LAST path is broken or the scenario
      mis-drives it. Drive a framed burst with `wide_last` held low — LAST can
      then only come from the counter (`test_burst_len_drives_last` in the TB
      does this and is currently unwired).
- [ ] If RTL: fix, with the failing test as the gate.
- [ ] If test: fix the framing units and the expectation.
- [ ] Either way, assert the return value so it can never silently fail again.
- [ ] Sweep for the same pattern: other scenarios whose result is discarded.


---

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
