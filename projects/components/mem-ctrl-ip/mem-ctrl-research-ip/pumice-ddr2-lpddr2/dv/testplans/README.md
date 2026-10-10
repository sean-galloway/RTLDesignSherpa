<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# DDR2/LPDDR2 Memory Controller Testplans

YAML testplans mapping every FUB/macro/top scenario to the cocotb test
that exercises it. Format mirrors the stream component's testplan
convention so the same coverage rollup scripts apply
(`bin/aggregate_coverage.py`, `bin/update_testplan_coverage.py`,
`bin/cov_utils/unified_coverage_report.py`).

## Inventory

Reconciled 2026-10-03 (pumice TASK-037): every `rtl_file` / `test_file`
below resolves, enforced by the testplan pass of
`bin/filelist_registry.py --check` (ratcheted baseline; a NEW broken ref
fails the gate). The pre-rearchitecture set lost 13 testplans whose
modules were dissolved or renamed without a 1:1 counterpart — deleted
rather than repointed at a vaguely similar block: `axi_intake` (split
into `pumice_rd_intake` + `pumice_wr_intake`), `wr_cmd_cam`,
`xbank_timers`, `wr2rd_forward`, `wr_beat_sequencer`, `rd_cl_aligner`,
`axi_id_side_table`, and the six macro wrappers (`axi_frontend_macro`,
`command_scheduler_macro`, `data_path_macro`, `dfi_v21_interface_macro`,
`pumice_core_macro`, `pumice_csr_slave`) whose hierarchies the AXI4
front-end rework dissolved. Three were renamed in place: `scheduler` ->
`pumice_scheduler_layer`, `rd_cmd_cam` -> `pumice_rd_cmd_cam`,
`page_predictor` -> `pumice_page_policy`.

Closed 2026-10-03 (pumice TASK-039): the 13 post-rearchitecture FUBs and
macros that had tests but no plans now have them (`pumice_cmd_arbiter`
17 scenarios incl. the issue-rate companion test, `pumice_bank_timers` 6,
`pumice_rd_intake` 3, `pumice_wr_intake` 8, `pumice_wr_data_cam` 9,
`pumice_rd_return_ring` 5, `pumice_wr_splitter` 4, `pumice_axi4_layer` 1,
and the DFI stack `pumice_dfi_cdc` 1 / `pumice_dfi_cmd_path` 2 /
`pumice_dfi_rd_aligner` 4 / `pumice_dfi_wr_serializer` 2 /
`pumice_dfi_layer` 1), plus a SCHED-24 matrix scenario in the scheduler
plan covering `test_pumice_sched_matrix.py`. Blocks and tests without
testplans are listed with rationale under "No-plan rationale" below.

### Unit level (direct unit tests)

| Testplan | Module | Test file | Scenarios |
|----------|--------|-----------|----------:|
| `scheduler_testplan.yaml` | pumice_scheduler_layer.sv | test_pumice_scheduler_layer.py, test_pumice_sched_matrix.py | 24 |
| `pumice_cmd_arbiter_testplan.yaml` | pumice_cmd_arbiter.sv | test_pumice_cmd_arbiter.py, test_pumice_arbiter_issue_rate.py | 17 |
| `refresh_ctrl_testplan.yaml` | refresh_ctrl.sv | test_refresh_ctrl.py | 10 |
| `pumice_wr_data_cam_testplan.yaml` | pumice_wr_data_cam.sv | test_pumice_wr_data_cam.py | 9 |
| `powerdown_ctrl_testplan.yaml` | powerdown_ctrl.sv | test_powerdown_ctrl.py | 9 |
| `pumice_bank_timers_testplan.yaml` | pumice_bank_timers.sv | test_pumice_bank_timers.py | 6 |
| `pumice_dfi_rd_aligner_testplan.yaml` | pumice_dfi_rd_aligner.sv | test_pumice_dfi_rd_aligner.py | 4 |
| `global_timers_testplan.yaml` | global_timers.sv | test_global_timers.py | 6 |
| `pumice_wr_splitter_testplan.yaml` | pumice_wr_splitter.sv | test_pumice_wr_splitter.py | 4 |
| `pumice_rd_return_ring_testplan.yaml` | pumice_rd_return_ring.sv | test_pumice_rd_return_ring.py | 5 |
| `pumice_wr_intake_testplan.yaml` | pumice_wr_intake.sv | test_pumice_wr_intake.py | 8 |
| `mode_register_testplan.yaml` | mode_register.sv | test_mode_register.py | 7 |
| `pumice_rd_intake_testplan.yaml` | pumice_rd_intake.sv | test_pumice_rd_intake.py | 3 |
| `init_sequencer_testplan.yaml` | init_sequencer.sv | test_init_sequencer.py | 4 |
| `rd_cmd_cam_testplan.yaml` | pumice_rd_cmd_cam.sv | test_pumice_rd_cmd_cam.py | 11 |
| `pumice_dfi_cmd_path_testplan.yaml` | pumice_dfi_cmd_path.sv | test_pumice_dfi_cmd_path.py | 2 |
| `pumice_dfi_wr_serializer_testplan.yaml` | pumice_dfi_wr_serializer.sv | test_pumice_dfi_wr_serializer.py | 2 |
| `dfi_cmd_formatter_testplan.yaml` | dfi_cmd_formatter.sv | test_dfi_cmd_formatter.py | 6 |
| `dfi_signal_pack_testplan.yaml` | dfi_signal_pack.sv | test_dfi_signal_pack.py | 4 |
| `addr_mapper_testplan.yaml` | addr_mapper.sv | test_addr_mapper.py | 4 |
| `page_predictor_testplan.yaml` | pumice_page_policy.sv | test_page_predictor.py | 5 |
| `pumice_axi4_layer_testplan.yaml` | pumice_axi4_layer.sv | test_pumice_axi4_layer.py | 1 |
| `pumice_dfi_cdc_testplan.yaml` | pumice_dfi_cdc.sv | test_pumice_dfi_cdc.py | 1 |
| `pumice_dfi_layer_testplan.yaml` | pumice_dfi_layer.sv | test_pumice_dfi_layer.py | 1 |

### Top level

| Testplan | Module | Test file | Scenarios |
|----------|--------|-----------|----------:|
| `pumice_top_testplan.yaml` | pumice_top.sv | test_pumice_top.py | 11 |

### No-plan rationale

Every FUB/macro block with a `dv/tests/fub|macro/` RTL test now has a
testplan (unit table above). The remaining uncovered items are:

- `pumice_axi_burst_chopper` — RTL FUB with **no direct unit test**. Both
  instantiation sites are exercised through other plans: the read side
  (`u_rd_split` in `pumice_axi4_layer.sv`) runs single-sub-command mode
  under `pumice_axi4_layer_testplan.yaml` AXI4-01, and the write side
  (`u_aw_chop` inside `pumice_wr_splitter`) split/pad/ragged behavior is
  covered by `pumice_wr_splitter_testplan.yaml` WSPL-01..04. A standalone
  plan would claim coverage the tests do not give.
- `pumice_cmd_history_checker` — debug scoreboard, compiled only when
  `CMD_HISTORY_EN=1` (off by default; instantiated inside
  `pumice_dfi_cmd_path` and `pumice_scheduler_layer`). No direct unit
  test.
- `test_pumice_config_array.py`, `test_pumice_telemetry_invariants.py`
  (fub/), `test_pumice_cmd_stream_checker.py` (macro/) — pure-Python
  checker/tooling unit tests with no DUT: they prove the covering array,
  telemetry rules, and JEDEC command-stream oracle can each fire, so they
  are not RTL functional-coverage subjects and get no testplan.

## Rollup

| Tier | Scenarios | Verified | % |
|------|----------:|---------:|--:|
| Unit (direct) | 153 | 153 | 100.0 |
| Top | 11 | 7 | 63.6 |
| **Total** | **164** | **160** | **97.6** |

"Verified" counts both `status: verified` and the older
`status: direct_verified` spelling (addr_mapper's four). The 4
unverified top-level entries are documented `status: debug_only`
cases (`bank0_probe`, `bank0_delayed`, `fresh_read_each_bank`,
`memory_preload_read`). They expose a downstream data-path hang on
fresh AXI reads that's distinct from the scheduler race fixed in
commit `66f32c7f`. They're tracked here for visibility but excluded
from the FUNC suite.

## FULL regression — per-file breakdown

The pre-rearchitecture per-file tables were removed with the dissolved
testplans they measured (2026-10-03, TASK-037); regenerate them with the
workflow below — each `test_*.py` at `TEST_LEVEL=FULL`, summed over its
parameterized combinations.

## Test pattern guarantees

Each surviving testplan includes scenarios that catch the **strict-flop
strobe race** class — see `docs/test_patterns_strobe_race.md`. The
scheduler S_DONE → S_IDLE bug (commit `66f32c7f`) lives behind:
- `scheduler.no_double_issue_wr / no_double_issue_rd / issued_pulse_width`
- `refresh_ctrl.grant_no_reissue`
- `powerdown_ctrl.grant_no_reissue`

The macro-level CAM-lag twin (`command_scheduler_macro.no_double_issue_race`)
retired with that testplan; the coverage now lives at unit level under
`scheduler_testplan.yaml`.

The pattern should be repeated for any future req/grant arbitration FUB.

## Rollup workflow

```bash
# Run with coverage
cd projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2
make coverage-fub-full     # COVERAGE=1 COVERAGE_LEGAL=1 TEST_LEVEL=full
make coverage-macro-full
make coverage-top-full

# Populate covers_lines: in YAMLs from Verilator .dat files
python3 ../../../../bin/update_testplan_coverage.py \
    --testplan dv/testplans/ \
    --coverage coverage_data/

# Aggregate per-module + report
python3 ../../../../bin/aggregate_coverage.py --all --html \
    --output coverage_reports/

# Verify functional coverage % vs scenario count
python3 ../../../../bin/cov_utils/verify_testplan_coverage.py \
    dv/testplans/
```

The `implied_coverage` block in each YAML is the functional-coverage
contribution. The `coverage_points` block (currently empty) gets
populated by `update_testplan_coverage.py` once Verilator runs land
their `.dat` files under `coverage_data/`.
