# TASK-039: author testplans for the post-rearchitecture FUBs

**Status:** closed 2026-10-03 (FIXED — see the CLOSED section below)
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

## CLOSED 2026-10-03

Authored the 13 missing testplans in `dv/testplans/` (63 new scenarios,
all gate-verified): `pumice_cmd_arbiter` (17, incl.
`test_pumice_arbiter_issue_rate.py` as ARB-17), `pumice_bank_timers` (6),
`pumice_rd_intake` (3), `pumice_wr_intake` (8, incl. the BL8 wrapper
variants), `pumice_wr_data_cam` (9), `pumice_rd_return_ring` (5),
`pumice_wr_splitter` (4), `pumice_axi4_ifc` (1), and the DFI stack
`pumice_dfi_cdc` (1), `pumice_dfi_cmd_path` (2), `pumice_dfi_rd_aligner`
(4), `pumice_dfi_wr_serializer` (2), `pumice_dfi_layer` (1). Added
SCHED-24 to the existing scheduler plan covering
`dv/tests/macro/test_pumice_sched_matrix.py` (12 operating points x 6
paging modes, JEDEC-checked). Rewrote `dv/testplans/README.md`: inventory
11 -> 24 plans, rollup 100 -> 164 scenarios (160 verified, 97.6%), plus a
"No-plan rationale" section for the exceptions:

- `pumice_axi_burst_chopper` — no direct unit test; both instantiation
  sites exercised via the `pumice_axi4_ifc` / `pumice_wr_splitter` plans.
- `pumice_cmd_history_checker` — `CMD_HISTORY_EN`-gated debug scoreboard,
  no direct unit test.
- `test_pumice_config_array.py`, `test_pumice_telemetry_invariants.py`,
  `test_pumice_cmd_stream_checker.py` — pure-Python checker tests, no DUT.

Same commit also fixed two pre-existing staleness bugs the review of this
work caught in `scheduler_testplan.yaml` (a TASK-037 rename leftover):
`test_file` pointed at `dv/tests/fub/` (macro is correct — this was one
of the 43 ratcheted broken refs; baseline re-lowered to 42), and the
`parameters` block named four parameters the RTL no longer has
(WR_CAM_DEPTH/RD_CAM_DEPTH/BURST_LEN_WIDTH/PAGE_POLICY) with a stale
AXI_ID_WIDTH default of 4 (RTL: 8). Verification: `bin/filelist_registry.
py --check` PASS; pumice gate `make run-all-gate` 193/194 — every test
referenced by the new plans passes (the one failure is the known
ISSUE-020 sched_cross pref_row_first perf floor, pre-existing).
