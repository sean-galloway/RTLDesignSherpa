# APB Monitor Test Structure

This document describes the focused test structure for APB monitor validation.

## Test Architecture

### Core Testbench (`apb_monitor_core_tb.py`)
- **Purpose**: Handles basic setup, configuration, and timing
- **Responsibilities**:
  - Clock and reset management
  - GAXI master/slave component initialization
  - Monitor bus slave setup
  - Ready signal pattern control
  - APB transaction sending/receiving
  - Configuration application to DUT

### Individual Test Files
Each test file focuses on ONE specific packet type with targeted configuration:

#### 1. Debug Events (`test_apb_debug.py`)
- **Tests**: Debug state transition events
- **Configuration**:
  - `debug_enable = True`
  - `trans_debug_enable = True` 
  - `debug_level = 0xF`
  - All other features disabled
- **Expected Events**: `APB.DEBUG.SETUP_PHASE`
- **Success Criteria**: Receives debug packets with correct event codes

#### 2. Completion Events (`test_apb_completion.py`)
- **Tests**: Successful transaction completion events
- **Configuration**:
  - `error_enable = True` (may be needed for completion detection)
  - `slverr_enable = True` (to distinguish error vs completion)
  - All debug/performance features disabled
- **Expected Events**: `APB.COMPLETION.TRANS_COMPLETE`
- **Success Criteria**: Receives completion packets for successful transactions

#### 3. Error Events (`test_apb_error.py`)
- **Tests**: Error detection (PSLVERR, protocol violations)
- **Configuration**:
  - `error_enable = True`
  - `slverr_enable = True`
  - `protocol_enable = True`
  - All other features disabled
- **Expected Events**: `APB.ERROR.PSLVERR`
- **Success Criteria**: Receives error packets when PSLVERR asserted

#### 4. Timeout Events (`test_apb_timeout.py`)
- **Tests**: Timeout detection for delayed transactions
- **Configuration**:
  - `timeout_enable = True`
  - `error_enable = True` (often needed for timeout detection)
  - Very short timeout thresholds (`cmd_timeout_cnt = 5`)
  - Delayed ready signal patterns
- **Expected Events**: `APB.TIMEOUT.SETUP` or `APB.TIMEOUT.ACCESS`
- **Success Criteria**: Receives timeout packets when transactions exceed thresholds

#### 5. Performance Events (`test_apb_performance.py`)
- **Tests**: Performance metric threshold violations
- **Configuration**:
  - `perf_enable = True`
  - `latency_enable = True`
  - `throughput_enable = True`
  - Very low thresholds (`latency_threshold = 50`)
  - Delayed ready signals to increase latency
- **Expected Events**: `APB.PERF.TOTAL_LATENCY` or `APB.PERF.THROUGHPUT`
- **Success Criteria**: Receives performance packets when thresholds exceeded

## Configuration Classes

### `APBMonitorConfiguration`
Centralizes all DUT configuration settings:
```python
config = APBMonitorConfiguration()
config.enable_debug_monitoring(trans_debug=True, debug_level=0xF)
config.set_timeouts(cmd_timeout=5, rsp_timeout=10)
```

### `ReadySignalPattern`
Controls ready signal timing:
```python
# Immediate ready (default)
ReadySignalPattern.immediate()

# Delayed ready to trigger timeouts/performance events
ReadySignalPattern.delayed(cmd_delay=10, rsp_delay=10)

# Random backpressure
ReadySignalPattern.random_backpressure()
```

## Running Tests

### Individual Test Execution
```bash
# Run specific test type
python test_apb_monitor.py debug
python test_apb_monitor.py completion
python test_apb_monitor.py error
python test_apb_monitor.py timeout
python test_apb_monitor.py performance
```

### Pytest Execution
```bash
# Run all focused tests
pytest test_apb_monitor.py

# Run specific test module
pytest test_apb_debug.py::test_apb_debug_events
pytest test_apb_completion.py::test_apb_completion_events
```

## Key Benefits

1. **Focused Testing**: Each test validates ONE specific monitor feature
2. **Clear Configuration**: Explicit enable/disable of specific features
3. **Isolated Debugging**: When a test fails, you know exactly which feature has issues
4. **Maintainable**: Easy to add new test types or modify existing ones
5. **Deterministic**: Each test has predictable expectations and configurations

## Troubleshooting

### If Debug Test Passes But Others Fail:
- Check that completion/error event generation is enabled in RTL
- Verify event generation priority in `apb_monitor.sv`
- Ensure correct packet type values in monitor bus output

### If No Packets Are Received:
- Check monitor bus connections in RTL
- Verify `monbus_valid` and `monbus_ready` handshaking
- Check that appropriate enable signals are connected

### If Wrong Packet Types Are Received:
- Verify the test configuration is being applied correctly
- Check DUT configuration registers are connected properly
- Review event generation logic priority in RTL

## Next Steps

1. **Start with Debug Test**: Since we know debug events work from your logs
2. **Add Completion Events**: Modify RTL if needed to generate completion packets
3. **Verify Error Detection**: Test with PSLVERR assertion
4. **Test Timeouts**: Use delayed ready signals
5. **Validate Performance**: Check threshold crossing detection

This structure makes it easy to validate each monitor feature independently and identify exactly what's working vs. what needs RTL changes.
