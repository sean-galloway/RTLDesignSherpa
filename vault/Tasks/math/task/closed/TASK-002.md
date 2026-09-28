# TASK-002: math_mod_3_compress needs its final formal checks

> Migrated 2026-09-27 from `vault/Tasks/math/closed.md` as **MATH-005** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-08-10 -- harness written per [[formal]]
(formal/common/math_mod_3_compress/): anyconst 16-bit input, rem_out asserted
against the solver's own `d_in % 3`, plus range assert and 7 covers (all three
residues, zero, all-ones/max digit sum, and both fold subtract branches --
digit sums 15 and 6). prove PASS, cover PASS 7/7 reached; mutation-checked
(fold constant 6->5 turns ap_rem_correct RED, restore GREEN).
**Priority:** P2
**Owner:** TBD

`math_mod_3_compress.sv` moved from rtl/common to rtl/math (commit 3ccd1fcd,
with filelist; registry PASS, no stale doc references). Reviews are done;
the formal checks remain. No harness exists yet (nothing under formal/
matches). Write the formal harness per [[formal]] (sv2v/SBY flow,
mutation rule, vacuity traps), fold the run into the formal backlog's
coverage, and close by pointing at passing proofs.

---
