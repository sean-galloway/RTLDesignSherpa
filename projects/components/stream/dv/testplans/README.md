# STREAM Testplan Directory

This directory contains YAML testplans mapping functional test scenarios to RTL coverage points for the STREAM subsystem.

## Overview

Testplans document:
- Module functionality and parameters
- Coverage points (ports, signals, logic)
- Functional test scenarios
- Parameter combinations tested
- Implied coverage calculations

Format follows `val/amba/testplans/` conventions for consistency across repository.

## Organization by Level

### FUB (Functional Unit Block) Level

Direct unit tests for individual modules:

| Testplan | Module | Status | Test File |
|----------|--------|--------|-----------|
| `apbtodescr_testplan.yaml` | apbtodescr.sv | Tested | test_apbtodescr.py |
| `descriptor_engine_testplan.yaml` | descriptor_engine.sv | Tested | test_descriptor_engine.py |
| `scheduler_testplan.yaml` | scheduler.sv | Tested | test_scheduler.py |
| `sram_controller_testplan.yaml` | sram_controller.sv | Tested | test_sram_controller.py |
| `stream_latency_bridge_testplan.yaml` | stream_latency_bridge.sv | Tested | test_stream_latency_bridge.py |

### FUB Level - Integration Tested Only

Modules tested via integration (no direct FUB test):

| Testplan | Module | Status | Rationale |
|----------|--------|--------|-----------|
| `axi_engines_testplan.yaml` | axi_read_engine.sv, axi_write_engine.sv | Integration tested | Complex streaming pipelines requiring full AXI + SRAM infrastructure. Tested via datapath_rd/wr_test and stream_core. |

### MACRO Level

| Testplan | Module | Status | Test File |
|----------|--------|--------|-----------|
| `stream_core_testplan.yaml` | stream_core.sv | Tested | test_stream_core.py |
| `scheduler_group_testplan.yaml` | scheduler_group.sv | Integration tested | Tested via stream_core (no direct macro test) |

### TOP Level

| Testplan | Module | Status | Test File |
|----------|--------|--------|-----------|
| `stream_top_testplan.yaml` | stream_top_ch8.sv | Tested | test_stream_top.py |

## Test Coverage Strategy

### Direct Testing (FUB Level)
- **apbtodescr**: 8 scenarios, 100% implied coverage
- **descriptor_engine**: 10 scenarios, 100% implied coverage
- **scheduler**: 11 scenarios, 100% implied coverage
- **sram_controller**: 11 scenarios, 100% implied coverage
- **stream_latency_bridge**: 9 scenarios, 100% implied coverage

### Integration Testing (MACRO Level)
- **axi_engines**: 11 scenarios via datapath_rd/wr_test and stream_core
- **scheduler_group**: 7 scenarios via stream_core
- **stream_core**: 12 scenarios (gate/func/full/burst levels)

### System Testing (TOP Level)
- **stream_top_ch8**: 13 scenarios (complete 8-channel DMA system)

## Gap Rationale

### axi_read_engine / axi_write_engine
**Gap**: No direct FUB-level tests

**Rationale**:
- Complex streaming pipelines requiring full infrastructure
- Direct testing would duplicate integration test effort
- Better coverage via integration tests at macro level

**Coverage Strategy**:
- Basic transfers: `test_datapath_rd_test.py`, `test_datapath_wr_test.py`
- Burst management: datapath tests
- Backpressure: `test_stream_core.py` (medium/full levels)
- Error handling: `test_stream_core.py` (error_injection)
- Concurrent operation: `test_stream_core.py` (concurrent)

**Result**: 100% functional coverage via integration testing

### scheduler_group
**Gap**: No direct MACRO-level test

**Rationale**:
- Simple wrapper around descriptor_engine + scheduler
- Both components have comprehensive FUB tests
- Full integration tested via stream_core

**Coverage Strategy**:
- Single channel flow: `test_stream_core.py` (gate level)
- Descriptor chains: `test_stream_core.py` (func level)
- Backpressure: `test_stream_core.py` (medium/full)
- Error handling: `test_stream_core.py` (error_injection)

**Result**: 100% functional coverage via integration testing

## Verilator Coverage Notes

Verilator coverage percentages appear low (~35-50%) because:
1. **Skid buffers and FIFOs**: Verilator doesn't track all internal state transitions
2. **Control logic**: FSM state coverage not fully captured
3. **AXI handshaking**: Valid/ready coordination logic undercounted

**Implied coverage** calculations show true functional coverage:
- All ports exercised
- All functional scenarios tested
- All error paths validated
- All parameter combinations verified

## Test Levels

STREAM uses hierarchical test levels:

### FUB Tests (Unit Level)
- **basic**: Single operation, minimal parameters
- **medium**: Multiple operations, parameter variations
- **full**: Stress testing, edge cases

### Integration Tests (System Level)
- **gate**: Quick smoke (2 descriptors, 1 channel, ~30s)
- **func**: Functional coverage (4 descriptors, 2 channels, ~90s)
- **full**: Comprehensive (16 descriptors, 4 channels, ~180s)
- **burst**: Burst matrix (6 descriptors, burst combinations, ~120s)

## Usage

### View Testplan
```bash
cat projects/components/stream/dv/testplans/scheduler_testplan.yaml
```

### Run Tests for Module
```bash
# FUB test
pytest projects/components/stream/dv/tests/fub/test_scheduler.py -v

# Integration test
pytest projects/components/stream/dv/tests/macro/test_stream_core.py -v
```

### Generate Coverage Report
```bash
# Run with coverage enabled
COVERAGE=1 pytest projects/components/stream/dv/tests/fub/ -v

# View aggregated report
cat coverage_data/aggregated/stream_coverage_report.txt
```

## Maintenance

When adding new modules or tests:
1. Create testplan YAML following existing format
2. Document all functional scenarios
3. Map scenarios to coverage points
4. Calculate implied coverage
5. Update this README

## References

- **Format Reference**: `/mnt/data/github/rtldesignsherpa/val/amba/testplans/axil4_slave_wr_testplan.yaml`
- **STREAM PRD**: `projects/components/stream/PRD.md`
- **Test Standards**: `/GLOBAL_REQUIREMENTS.md` Section 3 (Test Standards)
