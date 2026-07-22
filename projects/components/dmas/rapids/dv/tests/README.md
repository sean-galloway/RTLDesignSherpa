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

# RAPIDS Validation Test Suite - v2.0

> **Status (2026-07-22): superseded in part - pre-beats description.** The phase-1/2/3 layout
> below (`fub_tests/`, `integration_tests/`, `system_tests/`) and the tests it names were
> replaced by the beats test tree:
> `fub/` (control engines), `fub_beats/`, `macro/` (monbus group), `macro_beats/`, `top_beats/`.
> TB classes live in `projects/components/dmas/rapids/dv/tbclasses/` (NOT `bin/TBClasses/rapids/`,
> which no longer exists). Run `pytest projects/components/dmas/rapids/dv/tests/<suite>/ -v`.
> Historical descriptions are kept below for background.

This directory contains comprehensive validation tests for the RAPIDS system, following the established CocoTB framework methodology and leveraging the RAPIDS TB classes in `../tbclasses/`.

## Overview

The RAPIDS is a high-performance 2.5 GHz data streaming engine with four main macro blocks:

1. **Scheduler Group** - Dual FSM architecture with descriptor execution and address alignment
2. **Source Data Path** - Data transmission pipeline (DRAM → Network)
3. **Sink Data Path** - Data reception pipeline (Network → DRAM)
4. **MonBus AXI-Lite Group** - System monitoring and event aggregation

## Test Architecture

This test suite follows the user's guidance for proper TB organization:

- **TB Classes**: Located in `projects/components/dmas/rapids/dv/tbclasses/` with real GAXI/AXI4/AXIS/MonBus integration
- **Fixed 32-Channel Configuration**: All TBs use fixed 32-channel configuration for 32x scaling
- **Superset Testing**: Integration tests leverage multiple TB classes for unit-level validation
- **Organized FUB Tests**: Complex component tests organized in subdirectories to prevent clutter

## Test Structure

### Phase 1: FUB (Functional Unit Block) Tests

Organized individual component validation in `fub_tests/`:

#### Scheduler Components (`fub_tests/scheduler/`)
- `test_scheduler.py` - Main scheduler component validation
- `dual_fsm_scheduler_test.py` - Dual FSM architecture validation
- `alignment_bus_test.py` - Enhanced alignment bus interface testing
- `credit_management_test.py` - Credit return and management *(pending)*
- `program_sequencing_test.py` - Program sequence coordination *(pending)*

#### Descriptor Engine (`fub_tests/descriptor_engine/`)
- `test_descriptor_engine.py` - Main descriptor engine validation
- `apb_interface_test.py` - APB programming interface *(pending)*
- `descriptor_processing_test.py` - Descriptor data processing *(pending)*

#### Other FUB Components
- `fub_tests/program_engine/` - Program engine AXI write operations *(pending)*
- `fub_tests/axi_engines/` - Source/sink AXI read/write engines *(pending)*
- `fub_tests/sram_control/` - Source/sink SRAM control and buffering *(pending)*
- `fub_tests/network_interfaces/` - Network master/slave packet handling

### Phase 2: Integration Tests (`integration_tests/`)

**Framework TB Class Integration** - Tests that leverage existing TB classes:

- `test_scheduler_group_integration.py` - Uses `SchedulerGroupTB` from framework
- `test_source_datapath_integration.py` - Uses `SrcDatapathTB` from framework
- `test_sink_datapath_integration.py` - Uses `SnkDatapathTB` from framework
- `test_monbus_axil_integration.py` - Uses `MonbusAxilGroupTB` from framework

**Key Features:**
- ✅ **Real Component Integration**: Uses actual GAXI/AXI4/Network/MonBus factories
- ✅ **32-Channel Fixed Configuration**: All tests use 32 channels for scaling
- ✅ **Compliance Checking**: Built-in framework compliance validation
- ✅ **Performance Testing**: Timing profiles and stress testing

### Phase 3: System Tests (`system_tests/`)

**Superset Testing** - Demonstrates user's requested "superset tests that leverage all TBs":

- `test_end_to_end_system.py` - **Ultimate integration test using ALL TB classes**
  - Coordinates `SchedulerGroupTB`, `SrcDatapathTB`, `SnkDatapathTB`, `MonbusAxilGroupTB`
  - Tests complete RAPIDS system data flow
  - Validates 32x scaling simulation
  - Demonstrates cross-component coordination

**System Capabilities:**
- ✅ **Multi-TB Coordination**: All four TB classes working together
- ✅ **End-to-End Data Flow**: Complete system data path validation
- ✅ **32x Scaling Simulation**: Tests readiness for 32 scheduler group instantiation
- ✅ **Cross-Component Handoffs**: Validates component interaction and coordination

## Key Features Validated

### Enhanced RAPIDS v3.0 Features

- **Enhanced Alignment Bus Interface**: New RAPIDS package types (`alignment_info_t`, `transfer_phase_t`)
- **EOS-Only Boundary Support**: Removal of EOL/EOD signals throughout pipeline
- **Multi-Channel Operation**: Up to 32 concurrent channels with isolation
- **Monitor Bus Integration**: Comprehensive event generation and aggregation

### Performance Features

- **Address Alignment FSM**: Parallel operation for zero-cycle overhead
- **Credit-Based Flow Control**: Mathematical proof of zero packet loss
- **Pipeline Architecture**: Pure pipeline with minimal FSM overhead
- **Burst Optimization**: Pre-calculated alignment for optimal AXI performance

## Running Tests

### TB Class Integration Tests (Primary)

```bash
# Run macro-level tests (multi-block scenarios; the old integration_tests/ are gone)
pytest projects/components/dmas/rapids/dv/tests/macro_beats/ -v

# Run specific macro tests
pytest projects/components/dmas/rapids/dv/tests/macro_beats/test_scheduler_group_beats.py -v
pytest projects/components/dmas/rapids/dv/tests/macro_beats/test_src_data_path_axis_test_beats.py -v
pytest projects/components/dmas/rapids/dv/tests/macro_beats/test_snk_data_path_axis_test_beats.py -v
pytest projects/components/dmas/rapids/dv/tests/macro/test_monbus_axil_group.py -v

# Run top-level tests (the old system_tests/ are gone)
pytest projects/components/dmas/rapids/dv/tests/top_beats/ -v

# Run with specific test level
TEST_LEVEL=full pytest projects/components/dmas/rapids/dv/tests/macro_beats/test_scheduler_group_beats.py -v
```

### Test Levels

- **basic**: Core functionality validation (default)
- **medium**: Stress testing with error injection
- **full**: Comprehensive testing with all features

### Environment Configuration

```bash
# RAPIDS configuration
export RAPIDS_NUM_CHANNELS=8
export RAPIDS_DATA_WIDTH=512
export RAPIDS_ADDR_WIDTH=64
export TEST_LEVEL=basic
export ENABLE_WAVEDUMP=1
```

## Test Configuration

The test suite uses `conftest.py` for RAPIDS-specific configuration with these fixtures:

- `rapids_channel_config`: Channel count and sizing
- `rapids_data_config`: Data width and addressing
- `rapids_test_level`: Test complexity and coverage
- `rapids_timing_config`: Timing profiles for different scenarios
- `rapids_protocol_config`: Protocol feature enablement

## Markers

Tests are organized with pytest markers:

### Test Type Markers
- `@pytest.mark.fub`: FUB level tests
- `@pytest.mark.macro`: Macro block integration tests
- `@pytest.mark.integration`: System integration tests

### Component Markers
- `@pytest.mark.scheduler`: Scheduler component tests
- `@pytest.mark.descriptor`: Descriptor engine tests
- `@pytest.mark.network`: Network interface tests
- `@pytest.mark.monitor`: Monitor bus tests

### Performance Markers
- `@pytest.mark.performance`: Performance characterization
- `@pytest.mark.stress`: Stress testing

## Current Status

### ✅ Completed
- Test infrastructure and configuration
- Scheduler FUB validation (dual FSM architecture)
- Descriptor engine FUB validation (APB interface)
- Scheduler group macro integration (3-engine coordination)
- Network master FUB validation (packet transmission)
- Network slave FUB validation (packet reception)

### 🚧 In Progress
- Additional FUB tests for remaining engines
- Complete macro block integration tests
- End-to-end system validation

### 📋 Pending
- Program engine FUB validation
- AXI engine FUB validations (source read, sink write)
- SRAM control FUB validations (source, sink)
- Source/Sink data path macro integrations
- MonBus AXI-Lite group integration
- Performance characterization tests

## Implementation Notes

### Alignment Bus Interface

The enhanced alignment bus uses RAPIDS package types:

```systemverilog
typedef struct packed {
    logic                    is_aligned;
    logic [5:0]              addr_offset;
    logic [31:0]             first_transfer_bytes;
    logic [NUM_CHUNKS-1:0]   first_chunk_enables;
    logic [7:0]              optimal_burst_len;
    logic [31:0]             final_transfer_bytes;
    logic [NUM_CHUNKS-1:0]   final_chunk_enables;
    logic [3:0]              total_transfers;
    alignment_strategy_t     alignment_strategy;
} alignment_info_t;
```

### EOS-Only Support

The validation tests focus on EOS (End of Stream) boundaries only:
- EOL (End of Line) and EOD (End of Data) signals are not used
- EOS completion flows from SRAM control to scheduler
- Packet-level vs descriptor-level EOS differentiation

### Monitor Bus Events

All tests validate monitor bus event generation:
- Error events (timeout, protocol violations, parity errors)
- Performance events (alignment calculations, credit warnings)
- Completion events (data transfers, program operations)

## Dependencies

The test suite requires:
- CocoTB framework (installed in repository)
- RAPIDS RTL sources in `../rtl/`
- RAPIDS package definitions in `../rtl/includes/`
- Common utilities from `CocoTBFramework/`

## Logs and Artifacts

Test artifacts are preserved per suite (e.g. `dv/tests/fub_beats/logs/`, `dv/tests/macro_beats/logs/`, with builds in each suite's `local_sim_build/`):
- Pytest execution logs
- Verilator simulation logs
- Waveform files (if enabled)
- Coverage reports (if enabled)

## Integration with Repository

This validation suite follows the established patterns:
- Uses `TBBase` from `CocoTBFramework`
- Consistent test parametrization and configuration
- Integration with repository's build and test infrastructure
- Compatible with existing validation methodologies