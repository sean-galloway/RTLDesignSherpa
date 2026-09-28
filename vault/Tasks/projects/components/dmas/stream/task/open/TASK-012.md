# TASK-012: arm the 26 signal-contract maps that still render VERDICT: NOT CHECKED

**Status:** open 2026-09-27  **Priority:** P3 -- documentation evidence, no RTL
change. Filed from tooling TASK-006 when that global item closed: the shared
emitter in `bin/kmaps/` is done, stream's generator already imports it, and
stream TASK-001 armed the five priority maps (7 IDENTICAL, 1 DIFFERS -- a real
finding). 26 of 37 maps were left with no `rtl_sop=`, so the one criterion that
finds defects (derived cover vs the RTL as written) checks nothing on them.

For each remaining `kmap(...)` call in `docs/gen_signal_contracts_kmaps.py`:

1. `depends_only_on=` if missing: why the function depends on the axes alone.
2. `rtl_sop=`: the RTL expression as a sum-of-products over the axis names.
   A DIFFERS verdict is a finding -- redundant terms (say why they stay), an
   unstated invariant, or a bug -- and goes to this lane's bug list.

Multi-valued maps get item 1 only (no SOP is defined for them; the writer skips
the verdict on purpose). Spec: [[signal-contracts-and-kmaps]]. pumice's
equivalent is pumice TASK-029.

Acceptance: regenerated workbook has no `NOT CHECKED` row; every DIFFERS is
justified in the map's check text or filed as a stream BUG.
