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
`pumice_mem_cmd_scheduler`, `rd_cmd_cam` -> `pumice_rd_cmd_cam`,
`page_predictor` -> `pumice_page_policy`. Post-rearchitecture FUBs
(`pumice_cmd_arbiter`, `pumice_bank_timers`, the rd/wr intakes, the DFI
stack, ...) have tests but no testplans yet — that authoring gap is
pumice TASK-039.

### Unit level (direct unit tests)

| Testplan | Module | Test file | Scenarios |
|----------|--------|-----------|----------:|
| `scheduler_testplan.yaml` | pumice_mem_cmd_scheduler.sv | test_pumice_mem_cmd_scheduler.py | 23 |
| `refresh_ctrl_testplan.yaml` | refresh_ctrl.sv | test_refresh_ctrl.py | 10 |
| `powerdown_ctrl_testplan.yaml` | powerdown_ctrl.sv | test_powerdown_ctrl.py | 9 |
| `global_timers_testplan.yaml` | global_timers.sv | test_global_timers.py | 6 |
| `mode_register_testplan.yaml` | mode_register.sv | test_mode_register.py | 7 |
| `init_sequencer_testplan.yaml` | init_sequencer.sv | test_init_sequencer.py | 4 |
| `rd_cmd_cam_testplan.yaml` | pumice_rd_cmd_cam.sv | test_pumice_rd_cmd_cam.py | 11 |
| `dfi_cmd_formatter_testplan.yaml` | dfi_cmd_formatter.sv | test_dfi_cmd_formatter.py | 6 |
| `dfi_signal_pack_testplan.yaml` | dfi_signal_pack.sv | test_dfi_signal_pack.py | 4 |
| `addr_mapper_testplan.yaml` | addr_mapper.sv | test_addr_mapper.py | 4 |
| `page_predictor_testplan.yaml` | pumice_page_policy.sv | test_page_predictor.py | 5 |

### Top level

| Testplan | Module | Test file | Scenarios |
|----------|--------|-----------|----------:|
| `pumice_top_testplan.yaml` | pumice_top.sv | test_pumice_top.py | 11 |

## Rollup

| Tier | Scenarios | Verified | % |
|------|----------:|---------:|--:|
| Unit (direct) | 89 | 89 | 100.0 |
| Top | 11 | 7 | 63.6 |
| **Total** | **100** | **96** | **96.0** |

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
cd projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2
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
