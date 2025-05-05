# AXI Error Monitor Overview

## Introduction

The AXI Error Monitor module provides specialized verification components for detecting and reporting protocol errors in AXI (Advanced eXtensible Interface) bus interfaces. It focuses on monitoring timeout conditions and protocol violations, helping designers identify and debug issues in AXI-based designs.

Unlike general verification components, the AXI Error Monitor is designed specifically for error detection and reporting, serving as a layer that can be incorporated into larger verification environments.

## Architecture

The AXI Error Monitor consists of the following architectural components:

1. **Timeout Monitors**: Watch for stalled transactions in address, data, and response channels
2. **Error FIFO**: Buffer for storing detected errors
3. **Protocol Checkers**: Verify proper protocol sequencing and timing
4. **Multi-channel Support**: Independent monitoring for multiple parallel channels

### Operational Modes

The monitor supports two primary operational modes:

- **Read Mode**: Monitors address and data phases for read transactions
- **Write Mode**: Monitors address, data, and response phases for write transactions

### Error Types

The monitor detects and reports four primary error types:

1. **Address Timeout**: Address phase handshake not completed within timeout period
2. **Data Timeout**: Data phase handshake not completed within timeout period
3. **Response Timeout**: Response phase handshake not completed within timeout period (write mode only)
4. **Response Error**: SLVERR or DECERR response received from slave

## Test Environment

The test environment is structured as a hierarchy of test classes:

1. **Base TB Class**: Wrapper class that integrates all components
2. **Base Test Class**: Provides common utilities for all test types
3. **Specialized Test Classes**: Focus on specific aspects of functionality
   - Basic Test: Simple functionality
   - Error Test: Error detection
   - FIFO Test: Buffer behavior
   - Multichannel Test: Channel independence
   - Random Test: Randomized traffic

### Ready Signal Controller

A central component of the test environment is the Ready Signal Controller, which:

- Provides a single point of control for all ready signals
- Facilitates creating test scenarios for timeout and error conditions
- Handles back-pressure simulation
- Tracks signal transitions for verification

## Key Features

### Timeout Detection

Configurable timers monitor each AXI channel for stalled transactions:
- Counters initialized to maximum value
- Countdown while waiting for handshake completion
- Error reported if timer reaches zero

### Error Prioritization

When multiple errors occur simultaneously, the monitor prioritizes them:
1. Response errors (highest priority)
2. Address timeouts
3. Data timeouts
4. Response timeouts (lowest priority)

### FIFO Management

For write mode, a shared FIFO manages transaction tracking:
- Block ready signal assertion when FIFO is full
- Per-channel FIFOs in read mode
- Error FIFO for reporting detected errors

## Usage Example

### Basic Configuration

```python
# Create AXI Error Monitor testbench with configuration
tb = AXIErrorMonitorTB(
    dut,
    addr_width=32,
    id_width=8,
    is_read=True,      # Read mode
    timer_width=20,    # 20-bit timer width
    timeout_addr=1000, # 1000 cycle timeout for address
    timeout_data=1000, # 1000 cycle timeout for data
    timeout_resp=1000, # 1000 cycle timeout for response
    error_fifo_depth=4,
    addr_fifo_depth=4,
    channels=1
)

# Run tests
await tb.run_all_tests(test_level="basic")
```

### Custom Test Sequence

```python
# Create testbench
tb = AXIErrorMonitorTB(dut, ...)

# Reset DUT
await tb.reset_dut()

# Test basic transaction
transaction = await tb.basic_test.drive_basic_transaction(
    addr=0x1000,
    id_value=0,
    data_value=0xCAFEBABE,
    resp_value=0
)

# Test error scenario
await tb.error_test.drive_error_scenario(
    error_type='data_timeout',
    addr=0x2000,
    id_value=1
)

# Check detected errors
for error in tb.errors_detected:
    print(f"Error type: {error['type_str']}, ID: {error['id']}, Address: 0x{error['addr']:X}")
```

## Core Concepts

### Timeout Mechanism

Timeout detection is based on countdown timers:
- Timer initialized to MAX value (2^timer_width - 1)
- Timer decremented each cycle while waiting for transaction completion
- Error reported if timer reaches zero
- Timer reset and disabled when transaction completes

### Error Reporting

Errors are reported through a dedicated FIFO interface:
- Error type (4-bit): Bitfield indicating error type(s)
- Error ID: Transaction ID that encountered the error
- Error address: Address associated with the error

### Channel Independence

In multi-channel configurations:
- Each channel operates independently
- Channel selection based on transaction ID (ID % channels)
- Errors in one channel don't affect other channels
- Shared resources properly managed (for write mode)

## Implementation Notes

- Timers are configurable through parameters
- Support for AXI or AXI-Lite protocols
- Error FIFO can be configured with different depths
- Multiple channels share a common error reporting FIFO
- Support for various test levels (basic, medium, full)

## Best Practices

1. **Reset Before Testing**: Always reset the DUT before starting tests
2. **Error Handling**: Check error records after test scenarios
3. **Test Selection**: Use appropriate test level based on verification needs
4. **Protocol Compliance**: Verify error detection complies with AXI specification
5. **FIFO Management**: Ensure proper FIFO sizing for expected transaction volume

## See Also

- [AXI4 Components](../../components/axi4/index.md) - AXI4 protocol components
- [AXI4 Scoreboard](../../scoreboards/axi4_scoreboard.md) - AXI4 transaction verification

## Navigation

[↑ AXI Error Monitor Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
