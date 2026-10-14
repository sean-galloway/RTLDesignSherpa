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

**2026-10-13: the pumice area keeps one testplan.** Every FUB and macro
plane pumice instantiates is a common-ip `mc_*` module, and the owner ruled
that a pumice test points only at a pumice DUT. The 18 FUB/macro tests that
targeted common-ip modules (or the deleted `pumice_scheduler_plane`) were
removed, and the 15 testplans that mapped scenarios onto them went with them
-- a plan whose `test_file` does not exist fails the testplan pass of
`bin/filelist_registry.py --check`. They are in git history for whoever
writes the common-ip tests:

`scheduler`, `refresh_ctrl`, `init_sequencer`, `mode_register`,
`global_timers`, `dfi_cmd_formatter`, `rd_cmd_cam`, `pumice_bank_timers`,
`pumice_rd_intake`, `pumice_wr_intake`, `pumice_wr_data_cam`,
`pumice_rd_return_ring`, `pumice_wr_splitter`, `pumice_axi4_ifc`,
`pumice_dfi_plane`.

### Top level

| Testplan | Module | Test file | Scenarios |
|----------|--------|-----------|----------:|
| `pumice_top_testplan.yaml` | pumice_top.sv | test_pumice_top.py | 11 |

### No-plan rationale

- `test_pumice_core.py`, `test_pumice_core_dfi.py`, `test_pumice_top_csr.py`,
  `test_pumice_top_geared.py`, `test_pumice_config_sweep.py` (top/) -- pumice
  DUTs with no testplan yet.
- `test_pumice_config_array.py`, `test_pumice_telemetry_invariants.py`
  (fub/), `test_pumice_cmd_stream_checker.py` (macro/) and the `phy/` tests --
  pure-Python checker/tooling unit tests with no DUT: they prove the covering
  array, telemetry rules, JEDEC command-stream oracle and PHY read-window
  models can each fire, so they are not RTL functional-coverage subjects.

## Rollup

| Tier | Scenarios | Verified | % |
|------|----------:|---------:|--:|
| Top | 11 | 7 | 63.6 |

The 4 unverified top-level entries are documented `status: debug_only`
cases (`bank0_probe`, `bank0_delayed`, `fresh_read_each_bank`,
`memory_preload_read`). They expose a downstream data-path hang on
fresh AXI reads that's distinct from the scheduler race fixed in
commit `66f32c7f`. They're tracked here for visibility but excluded
from the FUNC suite.

## Test pattern guarantees

The strict-flop strobe race class is described in
`docs/test_patterns_strobe_race.md`. The unit-level guards that caught it
(`scheduler.no_double_issue_*`, `refresh_ctrl.grant_no_reissue`) left with
the common-ip tests above; re-establish them when those tests land in
common-ip. The pattern should be repeated for any future req/grant
arbitration FUB.

## Rollup workflow

```bash
# Run with coverage
cd projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2
make coverage-top-full     # COVERAGE=1 COVERAGE_LEGAL=1 TEST_LEVEL=full

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
