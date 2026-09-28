# TASK-014: COMMON-ORPHANS — two harnesses for RTL deleted a month earlier

> Migrated 2026-09-27 from `vault/Tasks/common/closed.md` as **FORMAL-INTEG** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-28 (opened same day)
**Priority:** was P3

`formal/integ_common/fifo_sync_multi/` and `fifo_sync_multi_sigmap/` listed
`../../../rtl/integ_common/*.sv`. That directory went with `rtl/integ_amba/` in
01d1c3e6. Deleted, along with their `formal_*.sv` wrappers.

They were the last two entries in `--blindspots`' `dead_harness_paths`, which
now reports PASS with **zero findings in all three classes** -- the first time
since the check was written (it opened at 516).

**Deleting them turned up two more pieces of the same residue**, in systems
nobody thought to look at:

  * `test_environments.toml` still declared `[env.val-integ-common]` and
    `[env.val-integ-amba]` pointing at `val/integ_common` / `val/integ_amba`,
    which do not exist. That file GENERATES `test_targets.mk`, which is tracked
    and carried 20 live make targets -- so `make test-val-integ-common` did not
    merely do nothing, it failed with `cd: val/integ_common: No such file`.
    Regenerated rather than hand-edited; 119 targets -> 99, exactly the 20 integ
    ones gone.
  * The four `apbx_xbar_*_wrap.sv` headers said `// Subsystem: integ_amba`,
    naming a dead subsystem that never described them anyway.

Which is the point worth keeping: AMBA-INTEG-EXAMPLES was closed after cleaning
the docs and `filelists.toml`, and that looked complete at the time. A deletion
leaves residue in every system that indexes code -- formal harnesses, test
environment config, generated make targets, file headers -- and each one is
found by a different check, or by none.
