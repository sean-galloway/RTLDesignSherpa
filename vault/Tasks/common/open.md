<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Open (accepted, not started)

---

## COMMON-010 — Every module MUST have a filelist and a registry entry
**Status:** open 2026-07-23

**The rule** (authority: [[filelists]]): every module in `rtl/common/` has a
filelist in `rtl/common/filelists/`, and the area is registered in
`bin/filelists.toml`. A new module lands with its `.f` **in the same commit** —
not "before the test lands". A module with no filelist has no consumers and is
indistinguishable from dead code the next time someone audits.

**Current state is good but unenforced.** `bin/filelist_registry.py --check`
reports common at 57 modules / 55 covered / 0 uncovered. The 2-module gap is
the `[exempt]` ledger, not a hole:

- `fifo_sync_multi` — multi-instance wrapper; no consumer yet
- `fifo_sync_multi_sigmap` — multi-instance wrapper; no consumer yet

**Work:**
1. Resolve the two exemptions: give each a filelist and a consumer, or drop the
   module. "No consumer yet" is a debt entry, not a permanent state.
2. Wire `--check` into a gate. **Nothing runs it today** — not the pre-commit
   hook, not CI (the only workflow is `track-clones.yml`), not a Makefile
   target. A MUST that nothing enforces is a wish. Shared with AMBA TASK-026;
   do the gate once for both.
3. When reading `--check` output, read all three numbers. It prints `PASS` when
   `declared - covered - exempt` is empty, so "55 covered" alongside "0
   uncovered" on a 57-module area is expected and still worth checking.


## COMMON-020 — the fifo_sync wavedrom generator produces no wave JSON
**Status:** open 2026-08-06 — found by the common test-audit round
**Priority:** P3 — no consumer is broken today

`val/common/test_fifo_sync_wavedrom.py` exists to emit timing diagrams. Its
`setup_wavedrom()` builds the `WaveJSONGenerator` and the interface groups, but
nothing ever calls `TemporalConstraintSolver.add_constraint()` — the only
registration path that reaches `_solve_temporal_constraint()` ->
`_create_solution_result()` -> `save_wavejson()`. The sampling loop iterates an
empty constraint set, no window is captured, and the run ends with

    WaveDrom Results: 0 solutions

then logged "GENERATION COMPLETE" and passed. The missing
`solve_and_generate()` call is now in place (its working sibling
`test_counter_bin_wavedrom` has one) and the celebration is replaced by a
warning, but the constraints themselves still have to be written.

**Why it is not asserted:** `docs/markdown/rtl-common/fifo_sync.md` tells the
reader to run the test rather than embedding committed JSON, so no doc is
missing a diagram today. A red test for an artifact nobody consumes trains
people to ignore red.

**Work:** port the constraint registration from the working reference,
`val/amba`'s gaxi fifo wavedrom test (which does emit JSON — see
`val/amba/local_sim_build/test_gw2_gaxi_fifo_sync_flop_wavedrom/*.json`), then
assert `len(results['solutions']) > 0` so the generator can never silently emit
nothing again.

---

## COMMON-021 — close the measured line-coverage gaps
**Status:** open 2026-08-07 — planned off the first real measurement
**Priority:** P2

Baseline: **93.3% line, 48 of 49 modules**, clean 932-test full run
(`COVERAGE=1 make run-all-full`). `arbiter_single_client` is exempt by
decision — verified in STREAM. Gate is 90.5%, so the depth mechanism is
demonstrably doing work; see the split below for where it is not.

### What the missing 6.7% actually is

**45 uncovered lines across 10 files: 20 are declarations, 25 are statements.**
Verilator emits coverage points on port and signal declarations, which are not
executable and can never be "covered". Roughly **45% of the apparent gap is
therefore an artifact** — three modules (`pwm`, `shifter_lfsr`,
`shifter_lfsr_fibonacci`) have ZERO uncovered statements and need no work at
all. Chasing a headline number without this split would spend effort on
nothing.

### Real gaps, in priority order

**1. `counter_bin_load` — 67.9%, 4 statements. The whole add path is dead.**
`add_enable`, `add_value` and every line of the variable-increment branch
(L154-164) are never exercised: the test only ever increments by one. This is
the single biggest real gap in the area, and it is a missing SCENARIO, not
missing depth — gate and full cover identically, so running it ten times
longer reaches the same lines.
Add: variable-increment stimulus, including a step that crosses `WRAP_BOUNDARY`
(L159/L161 are the wrap-on-add branch) and a step that does not.

**2. `counter_freq_invariant` — 71.1%, 9 statements. One selector mode untested.**
The whole `pow2_freq` function (L157-167) and the `1:` case that reaches it
(L173) never run — only the linear frequency table is exercised. Also
identical at gate and full.
Add: a `FREQ_SEL_MODE`-equivalent parameter sweep covering the power-of-2
table, including the `v >= hi` clamp (L163) and the `n <= 1` guard (L151).

**3. `shifter_universal` — 89.5%, 4 statements. X-handling default arm.**
The `default:` case that holds state on an X select (L78-81). Reachable in
simulation by driving X onto the select, which is a legitimate and cheap test.
Decide deliberately: cover it, or record that X-injection is out of scope for
this area and accept the ceiling.

**4. `leading_one_trailing_one` — 87.5%, 2 statements.** The
`int'(leadingone) < WIDTH` / `trailingone` guards (L102/L106) — the
found-nothing versus found-something boundary. Likely needs an all-zeros input
case.

**5. `find_first_set`, `find_last_set`, `encoder_priority_enable` — 2 statements each. VERIFY BEFORE WRITING ANYTHING.**
The uncovered lines sit inside unrolled `always_comb` for-loops
(`index = i[N-1:0]; w_found = 1'b1;`) that the existing tests must already
execute — these tests pass and the modules work. Establish first whether
Verilator attributes hits oddly for unrolled combinational loops. **If it is an
artifact, the correct action is to record that and move on, not to invent
scenarios for lines that already run.** Do not assume; measure with a directed
single-bit case and check whether the count moves.

### Non-goals

- **Do not chase the 20 declaration lines.** They are not executable.
- **Do not target 100%.** With ~20 artifact lines in the denominator the
  achievable ceiling is roughly 97-98%, and the last points buy nothing.

### Protocol (functional) coverage: decide, do not ignore

Reports 0.0% against an 80% target and has since the metric existed, because
nothing in `val/common` feeds it — it is for monbus packet-type matrices.
Either wire it or scope the target to the areas it applies to. A permanently
red metric trains people to ignore the whole report, which is how the coverage
mechanism came to be broken for this long in the first place.

### Sequencing

1. Verify the loop-artifact question (item 5) — it decides whether 6 of the 25
   statements are even actionable.
2. `counter_bin_load` and `counter_freq_invariant` — 13 of 25 statements, both
   pure scenario gaps, both with identical gate/full coverage today.
3. `shifter_universal` and `leading_one_trailing_one` — small, decide-then-do.
4. Re-measure and update `testplans/COVERAGE_REPORT.md`.

**Method note.** Every coverage number in this area was fiction until
2026-08-07 (see COVERAGE_REPORT.md: collection was never wired, the merge
dropped files, one wrapper built outside the glob). Re-measure after each
change rather than reasoning about what a scenario "should" cover.

---

## COMMON-003 — Create integration examples
**Status:** open — not started (migrated from rtl/common/TASKS.md, P2)

Standalone integration examples showing common usage patterns that combine
multiple common modules. Location: `rtl/integ_amba/examples/`.

Proposed:
- Example 1: state machine with timeout (counter + FSM)
- Example 2: multi-master system (arbiter + counters)
- Example 3: CRC-checked packet buffer (CRC + FIFO)
- Example 4: CDC data transfer (sync + handshake + FIFO)
- Example 5: simple PWM generator (counter + comparator)

Deliverables: 5 standalone designs, a test for each, documentation explaining
the design choices, and a README index. Success = all compile cleanly, all
tests pass, docs complete.


## COMMON-006 — Configurable-width adders/multipliers
**Status:** open — deferred pending user feedback, P3

Complex adders/multipliers are generated by Python in `bin/rtl_generators/`.
Parameterized SystemVerilog versions in the library were considered. Current
generation works well and parameterized versions may synthesise less optimally;
this is an educational-value vs practicality trade-off. Kept as open rather
than dropped because the decision was "not now", not "no".

## COMMON-007 — Additional arbiter types
**Status:** open — deferred pending user requests, P3

Token bucket, deficit round-robin, hierarchical arbitration. Current arbiters
cover ~95% of use cases and complex arbiters tend to be application-specific.

## COMMON-008 — Multi-byte CRC support
**Status:** open — deferred pending performance requirements, P3

`dataint_crc.sv` processes one byte per cycle. A 2/4/8/16-byte-per-cycle option
would serve high-throughput consumers, at an area cost.

## COMMON-009 — BCH and Reed-Solomon ECC
**Status:** open — deferred, P3. **Re-check before starting.**

Library ECC is Hamming SECDED only; BCH and Reed-Solomon were deferred as niche
(NAND flash, deep-space comms). A `projects/components/bch/` component once
existed as a docs-only placeholder (PRD/README/TASKS, no RTL and no tests) and
was **deleted 2026-07-23**, so this task is NOT superseded — it is the only
place BCH is tracked.
