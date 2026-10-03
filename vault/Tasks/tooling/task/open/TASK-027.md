# TASK-027: 43 broken testplan refs outside pumice (ratcheted baseline in place)

**Status:** open 2026-10-03
**Priority:** P3
**Filed from:** closing pumice TASK-037 (testplan reconcile).

pumice TASK-037 added a testplan pass to `bin/filelist_registry.py
--check`: every `*_testplan.yaml` `rtl_file`/`test_file` must resolve,
repo-wide, ratcheted against `bin/testplan_refs_baseline.json` — a NEW
broken ref fails pre-commit and CI; outstanding debt fails nobody. The
first baseline records 43 broken refs that predate the gate:

- `val/common/testplans`: 32
- `projects/components/fabric-gen-ip` (bridge + apbx-xbar): 9
- `val/amba/testplans`: 2

Fix per area with the same update-or-delete judgment TASK-037 used:
rename in place where a 1:1 counterpart exists, delete plans for
dissolved modules, and do not repoint a plan at a vaguely similar block.
Then lower the baseline:

    python3 bin/filelist_registry.py --testplans --update-testplan-baseline

The gate prints the IMPROVED list as refs are fixed, so this can be done
incrementally across sessions.
