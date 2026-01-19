# RAPIDS Testplan Index

Quick reference mapping RTL modules to testplans and test files.

---

## FUB Legacy (6 modules)

| RTL Module | Testplan | Test File | Coverage |
|------------|----------|-----------|----------|
| ctrlrd_engine.sv | ctrlrd_engine_testplan.yaml | fub/test_ctrlrd_engine.py | 100% (9 scenarios) |
| ctrlwr_engine.sv | ctrlwr_engine_testplan.yaml | fub/test_ctrlwr_engine.py | 100% (7 scenarios) |
| sink_axi_write_engine.sv | fub_legacy_gaps_testplan.yaml | (integration-tested) | GAP |
| sink_sram_control.sv | fub_legacy_gaps_testplan.yaml | (integration-tested) | GAP |
| source_axi_read_engine.sv | fub_legacy_gaps_testplan.yaml | (integration-tested) | GAP |
| source_sram_control.sv | fub_legacy_gaps_testplan.yaml | (integration-tested) | GAP |

---

## FUB Beats (7 modules)

| RTL Module | Testplan | Test File | Coverage |
|------------|----------|-----------|----------|
| alloc_ctrl_beats.sv | alloc_ctrl_beats_testplan.yaml | fub_beats/test_alloc_ctrl_beats.py | 100% (5 scenarios) |
| axi_read_engine_beats.sv | data_path_beats_testplan.yaml | (integration-tested) | 100% |
| axi_write_engine_beats.sv | data_path_beats_testplan.yaml | (integration-tested) | 100% |
| descriptor_engine_beats.sv | descriptor_engine_beats_testplan.yaml | fub_beats/test_descriptor_engine_beats.py | 100% (7 scenarios) |
| drain_ctrl_beats.sv | drain_ctrl_beats_testplan.yaml | fub_beats/test_drain_ctrl_beats.py | 100% (5 scenarios) |
| latency_bridge_beats.sv | latency_bridge_beats_testplan.yaml | fub_beats/test_latency_bridge_beats.py | 100% (5 scenarios) |
| scheduler_beats.sv | scheduler_beats_testplan.yaml | fub_beats/test_scheduler_beats.py | 100% (11 scenarios) |

---

## MACRO Beats (13 modules)

| RTL Module | Testplan | Test File | Coverage |
|------------|----------|-----------|----------|
| rapids_core_beats.sv | (integration-tested) | (system-level) | 100% |
| scheduler_group_array_beats.sv | (integration-tested) | macro_beats/test_scheduler_group_array_beats.py | 100% |
| scheduler_group_beats.sv | scheduler_group_beats_testplan.yaml | macro_beats/test_scheduler_group_beats.py | 100% (4 scenarios) |
| snk_data_path_axis_beats.sv | data_path_beats_testplan.yaml | macro_beats/test_snk_data_path_axis_test_beats.py | 100% |
| snk_data_path_axis_test_beats.sv | data_path_beats_testplan.yaml | macro_beats/test_snk_data_path_axis_test_beats.py | 100% |
| snk_data_path_beats.sv | (integration-tested) | (system-level) | 100% |
| snk_sram_controller_beats.sv | data_path_beats_testplan.yaml | macro_beats/test_snk_sram_controller_beats.py | 100% |
| snk_sram_controller_unit_beats.sv | data_path_beats_testplan.yaml | (via snk_sram_controller) | 100% |
| src_data_path_axis_test_beats.sv | data_path_beats_testplan.yaml | macro_beats/test_src_data_path_axis_test_beats.py | 100% |
| src_data_path_beats.sv | (integration-tested) | (system-level) | 100% |
| src_data_path_axis_beats.sv | data_path_beats_testplan.yaml | macro_beats/test_src_data_path_axis_test_beats.py | 100% |
| src_sram_controller_beats.sv | data_path_beats_testplan.yaml | macro_beats/test_src_sram_controller_beats.py | 100% |
| src_sram_controller_unit_beats.sv | data_path_beats_testplan.yaml | (via src_sram_controller) | 100% |

---

## Directory Structure

```
projects/components/rapids/
├── rtl/
│   ├── fub/                           # FUB Legacy modules
│   ├── fub_beats/                     # FUB Beats modules
│   └── macro_beats/                   # MACRO Beats modules
├── dv/
│   ├── testplans/                     # THIS DIRECTORY
│   │   ├── README.md                  # Full documentation
│   │   ├── TESTPLAN_INDEX.md          # This file
│   │   ├── *_testplan.yaml           # Individual testplans
│   │   └── fub_legacy_gaps_testplan.yaml  # Testing gaps
│   ├── tests/
│   │   ├── fub/                       # FUB Legacy tests
│   │   ├── fub_beats/                 # FUB Beats tests
│   │   └── macro_beats/               # MACRO Beats tests
│   └── tbclasses/                     # Testbench classes
└── docs/                              # RAPIDS specification
```

---

## Usage

### View Specific Testplan

```bash
# FUB Legacy
cat ctrlrd_engine_testplan.yaml
cat fub_legacy_gaps_testplan.yaml

# FUB Beats
cat scheduler_beats_testplan.yaml
cat descriptor_engine_beats_testplan.yaml

# MACRO Beats
cat scheduler_group_beats_testplan.yaml
cat data_path_beats_testplan.yaml
```

### Run Tests for Specific Module

```bash
# FUB Legacy
pytest projects/components/rapids/dv/tests/fub/test_ctrlrd_engine.py -v

# FUB Beats
pytest projects/components/rapids/dv/tests/fub_beats/test_scheduler_beats.py -v

# MACRO Beats
pytest projects/components/rapids/dv/tests/macro_beats/test_scheduler_group_beats.py -v
```

### View Coverage Summary

```bash
cat README.md
```

---

## Quick Stats

- **Total Modules:** 26
- **Total Testplans:** 10 (8 individual + 2 group testplans)
- **Total Functional Scenarios:** 67
- **FUB-Level Coverage:** 85% (22/26 modules)
- **Integration-Level Coverage:** 100% (26/26 modules)

---

**Last Updated:** 2026-01-18
