# TASK-010: close the measured line-coverage gaps

> Migrated 2026-09-27 from `vault/Tasks/common/closed.md` as **COMMON-024** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-08 (5c013326) — planned off the first real
measurement. Re-verified 2026-09-01: `val/common/test_counter_bin_load.py`
now covers the `add_enable` variable-increment path and both wrap arms,
which was the single biggest real gap.
**Priority:** P2
**ID note:** filed as COMMON-021, which was already taken by the formal
staleness-audit task closed the following day. Renumbered 2026-09-01;
commits and prose from 2026-08-07/08 that say COMMON-021 and talk about
coverage mean this task.

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

**CLOSED 2026-08-08 — 95.3% line (95.7% statements), and the rest is unreachable.**

The verify-before-writing step paid for itself: of the 25 statements the plan
listed, **10 turned out to be a Verilator attribution artifact**, not gaps.
`leading_one_trailing_one` settled it -- its `if` guard reports 0 hits while
the body INSIDE it reports 136628. No test can cover those, and writing one
would have been pure waste.

Two real gaps closed:

- `counter_bin_load` **67.9% -> 92.9%**: the whole `add_enable` branch was dead
  because the test only ever incremented by one. Added variable increment
  across both wrap arms plus the load > add > enable priority.
- `counter_freq_invariant` **71.1% -> 89.5%**: `FREQ_STRATEGY` was pinned at
  LINEAR so `pow2_freq` never elaborated. Now a grid dimension, with a
  single-entry LUT config for the degenerate case the RTL explicitly supports.
  Its test name had to grow the strategy too -- without it the LINEAR and POW2
  builds shared one sim_build directory and the second reused the first's DUT.

**One test was written and then deleted the same day.** `shifter_universal`'s
`default:` arm handles an X select, and driving `BinaryValue('xx')` in Verilator
-- a 2-STATE simulator -- resolves to a defined value, so the arm stayed at
zero hits while the test passed. It was silently exercising `select=00`, the
hold case, and asserting state was held. Removing it was the right call: a test
that passes by testing something other than its name is worse than none, and
this area spent a week removing exactly that.

All 20 remaining uncovered statements are in three understood classes --
nested-statement attribution, `default:` arms unreachable in 2-state, and
elaboration-time functions. **Line coverage for this area is complete**; what
is left is tooling behaviour, not test debt.

---
