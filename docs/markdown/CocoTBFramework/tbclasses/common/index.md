# Common Test Classes

## Overview

The `tbclasses/common` module provides reusable test classes for common digital logic components. These classes implement standardized verification approaches for frequently used components like adders, multipliers, FIFOs, and more. They serve as both reference implementations and ready-to-use building blocks for integration into larger verification environments.

## Key Features

- Standardized test approaches for common digital components
- Comprehensive parameter-driven configurations
- Flexible test levels (basic, medium, full)
- Randomized and directed test capabilities
- Built-in reporting and statistics tracking
- Clear patterns for creating custom test components

## Module Components

- [Adder Testing](adder_testing.md) - Test classes for various adder implementations
- [CAM Testing](cam_testing.md) - Test classes for Content Addressable Memory verification
- [CRC Testing](crc_testing.md) - Test classes for Cyclic Redundancy Check modules
- [Divider Testing](divider_testing.md) - Test classes for various divider implementations
- [Multiplier Testing](multiplier_testing.md) - Test classes for various multiplier implementations
- [Subtractor Testing](subtractor_testing.md) - Test classes for various subtractor implementations
- [AMBA Clock Gate Controller](amba_cg_ctrl.md) - Test utilities for AMBA clock gating

## Usage Guide

- [Overview](overview.md) - Introduction and usage guidelines

## Basic Usage Pattern

All common test classes follow a similar pattern:

```python
from CocoTBFramework.tbclasses.common import adder_testing

@cocotb.test()
async def test_adder(dut):
    # Create testbench with DUT
    tb = adder_testing.AdderTB(dut)
    
    # Print current settings
    tb.print_settings()
    
    # Run comprehensive tests at desired level
    await tb.run_comprehensive_tests()
```

## Extending the Common Test Framework

Creating a new common test class involves:

1. Inheriting from `TBBase`
2. Implementing standard configuration handling
3. Creating test methods for component-specific functionality
4. Creating a comprehensive test method that combines individual tests
5. Adding reporting and statistics tracking

See the [overview](overview.md) for more details on implementation patterns.

## Test Levels

The common test classes support different test levels:

- **basic**: Simple functional tests with limited randomization
- **medium**: More extensive tests with moderate randomization
- **full**: Comprehensive tests with extensive randomization and corner cases

This allows users to balance test thoroughness against execution time.

## See Also

- [TBBase](../tbbase.md) - Base class for all testbench components
- [Utilities](../utilities.md) - Common utility functions

## Navigation

[↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
