# ISSUE-003: required-regen fixes can drag unrelated changes into a commit — mitigation protocol

**Priority:** P3
**Status:** OPEN (process/hygiene; resolves into ISSUE-002's reconcile + a convention note)
**Owner:** TBD

## The episode (2026-10-10, BUG-008)

BUG-008's fix required regenerating `math_fp8_e4m3_to_fp8_e5m2.sv` from
`bin/rtl_generators/ieee754/generate_all.py`. The documented command
regenerates **all 115 modules**, and ~115 files came back dirty even though
the fix touched one template branch:

1. `// Created: <date>` header stamps move to the regen day on every file.
2. A real template/RTL divergence: sequential modules regenerate with plain
   `always_ff @(posedge i_clk or negedge i_rst_n)` while the committed RTL
   uses the `reset_defs.svh` macros (`ALWAYS_FF_RST`, `RST_ASSERTED`) — the
   committed files were not produced by the current generator state.

The commit-path risk: either ~115 unrelated files ride along in a surgical
bug-fix commit, or they must be hand-reverted (what happened — restored all
but the one intended module via pathspec-excluded checkout). Both options
are error-prone under time pressure, and the trap will re-open on every
future generator fix until the drift is reconciled.

## Mitigation (agreed direction)

Ranked, root-cause first:

1. **Reconcile the drift** (ISSUE-002): one dedicated "generator reconcile"
   commit — run the full regen, review the reset-macro delta across the
   sequential modules, land it on its own. After that, the documented regen
   is a no-op diff for unchanged templates and this issue's trap closes
   with it.
2. **Stop stamping dates on regen**: the generator should write `Created:`
   only when the file does not already exist (or take the date from the
   existing file), so future template fixes produce minimal diffs by
   construction.
3. **Protocol until 1+2 land — required regen produces unrelated drift:**
   - never `git add -A` / bare `git commit` after a regen;
   - review `git status rtl/math`, restore everything except the intended
     files (`git checkout -- rtl/math ':!<intended>'`), and state the
     revert in the commit message;
   - if the unrelated drift is substantive (not just dates), stop and file
     an issue instead of silently reverting — it may be uncommitted someone-
     else's work or a second real bug.
4. **Candidate CI gate (defer until after the reconcile):** a lightweight
   check that `generate_all.py` output matches committed RTL would make
   drift visible the day it appears instead of at the next regen. Only
   worth building if the reconcile holds — otherwise it just noisily
   re-detects ISSUE-002.

## Context: what the regen was for

- **BUG-008** (fixed same session): `math_fp8_e4m3_to_fp8_e5m2` NaN'd the
  top of the e4m3 range (exp=15, mant=1..6; 264..448 incl. max-normal) —
  narrowing conversion templates hardcoded the infinity-style source decode.
- **TASK-007** (fixed same session): the special-value Cartesian product
  grid that caught BUG-008 on first landing, plus the clamp comparator
  contract now encoded in the FPClampTB golden.
- **ISSUE-002** (open): the drift itself, which this issue's item 1 closes.

## Log

**2026-10-10 -- filed** at Sean's request after the BUG-008/TASK-007 work,
to capture both the found/fixed items and the unrelated-change mitigation.
