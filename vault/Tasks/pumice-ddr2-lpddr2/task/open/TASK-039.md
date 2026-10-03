# TASK-039: author testplans for the post-rearchitecture FUBs

**Status:** open 2026-10-03
**Priority:** P3
**Filed from:** closing TASK-037 (testplan reconcile).

TASK-037 reconciled the 25 pre-rearchitecture testplans down to 12 that
match modules which exist (3 renamed in place, 13 deleted as dissolved).
What it deliberately did NOT do is author plans for the blocks the
rearchitecture added or the axi_intake split created — they have tests
but no testplans:

- `pumice_cmd_arbiter` (`test_pumice_cmd_arbiter.py`, plus
  `test_pumice_arbiter_issue_rate.py`)
- `pumice_bank_timers` / `bank_timer` (`test_pumice_bank_timers.py`)
- `pumice_rd_intake` + `pumice_wr_intake` — the `axi_intake` split; its
  old testplan was deleted rather than repointed, so both children are
  uncovered at plan level
- `pumice_wr_data_cam`, `pumice_rd_return_ring`, `pumice_wr_splitter`
- `pumice_axi_burst_chopper`, `pumice_axi4_ifc`
- the DFI stack: `pumice_dfi_cdc`, `pumice_dfi_cmd_path`,
  `pumice_dfi_layer`, `pumice_dfi_rd_aligner`,
  `pumice_dfi_wr_serializer`

`pumice_mem_cmd_scheduler` already has one (the renamed scheduler plan).

Format: mirror the surviving YAMLs in `dv/testplans/`. Refs are
gate-checked by `bin/filelist_registry.py --check` (TASK-037), so a new
plan with a bad `rtl_file`/`test_file` fails pre-commit; the
`functional_scenarios`/`implied_coverage` blocks follow the existing
convention and are what `bin/update_testplan_coverage.py` consumes.

**Done when:** every FUB/macro block with a `dv/tests/fub|macro/` test
has a testplan, or `dv/testplans/README.md` carries an explicit
no-plan rationale for the exceptions.
