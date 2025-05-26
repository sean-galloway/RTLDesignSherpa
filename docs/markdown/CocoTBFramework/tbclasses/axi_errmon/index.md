# AXI Error Monitor

## Overview

The AXI Error Monitor (errmon) module provides verification components for detecting and reporting protocol errors in AXI bus interfaces. This specialized module focuses on timeout detection, error reporting, and protocol verification for both AXI read and write interfaces.

## Key Features

- Timeout detection for AXI address, data, and response phases
- Error reporting via dedicated error FIFO
- Support for both read and write mode operations
- Verification of AXI protocol compliance
- Configurable timeout settings
- Multi-channel support

## Module Components

- [AXI Error Monitor Base TB](axi_errmon_base_tb.md) - Main testbench wrapper class
- [AXI Error Monitor Base Test](axi_errmon_base_test.md) - Base test class with common utilities
- [AXI Error Monitor Basic Test](axi_errmon_basic_test.md) - Fundamental operation tests
- [AXI Error Monitor Error Test](axi_errmon_error_test.md) - Error scenario tests
- [AXI Error Monitor FIFO Test](axi_errmon_fifo_test.md) - FIFO behavior tests
- [AXI Error Monitor Multichannel Test](axi_errmon_multichannel_test.md) - Multi-channel tests
- [AXI Error Monitor Random Test](axi_errmon_random_test.md) - Randomized traffic tests
- [AXI Error Monitor Ready Controller](axi_errmon_readyctrl.md) - Control for ready signals

## Usage Guide

- [Overview](overview.md) - Introduction and usage guidelines

## Basic Usage

```python
from CocoTBFramework.tbclasses.axi_errmon.axi_errmon_base_tb import AXIErrorMonitorTB

@cocotb.test()
async def test_axi_error_monitor(dut):
    # Create testbench wrapper with configuration
    tb = AXIErrorMonitorTB(
        dut,
        addr_width=32,
        id_width=8,
        is_read=True,  # Read mode
        timer_width=20,
        timeout_addr=1000,
        timeout_data=1000,
        timeout_resp=1000,
        channels=1
    )
    
    # Run all tests
    all_passed = await tb.run_all_tests(test_level="medium")
    
    # Report test results
    if all_passed:
        dut._log.info("All tests passed")
    else:
        dut._log.error("Some tests failed")
```

## Test Levels

The AXI Error Monitor supports different test levels:

- **basic**: Simple operational tests and FIFO tests
- **medium**: Adds error detection tests and moderate random testing
- **full**: Adds multi-channel tests and extensive random testing

## See Also

- [AXI4 Components](../../components/axi4/index.md) - AXI4 protocol components
- [AXI4 Scoreboard](../../scoreboards/axi4_scoreboard.md) - AXI4 transaction verification

## Navigation

[↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
