# APB Test Classes

## Overview

The `tbclasses/apb` module provides AMBA APB (Advanced Peripheral Bus) protocol testing classes and utilities. These components focus on register map testing, command handling, and functional verification of APB interfaces.

## Key Features

- Advanced register map handling with UVM integration
- Command/response interface processing for APB slave testing
- Functional testing with simplified tuple-based register verification
- Comprehensive register test factory for various test types
- Register structure documentation and validation

## Module Components

- [APB Command Handler](apb_command_handler.md) - Command/response processing for APB slaves
- [Register Map](register_map.md) - Register information handling and access
- [Register Map Structure](register_map_structure.md) - Register definition data format
- [Register Functional Testing](register_functional_testing.md) - Tuple-based functional testing
- [Register Test Factory](register_test_factory.md) - Factory functions for comprehensive register tests

## Usage Guide

- [Overview](overview.md) - Introduction and usage guidelines

## Basic Usage

```python
from CocoTBFramework.tbclasses.apb.register_map import RegisterMap
from CocoTBFramework.tbclasses.apb.register_test_factory import create_register_test_sequence

@cocotb.test()
async def test_register_access(dut):
    # Create register map from UVM file
    reg_map = RegisterMap(
        filename="registers.py",
        apb_data_width=32,
        apb_addr_width=24,
        start_address=0x7F0000,
        log=dut._log
    )
    
    # Create walking ones test
    sequence = create_register_test_sequence(
        reg_map,
        test_type="walk",
        options={
            "pattern": "walking_ones",
            "delay": 2
        }
    )
    
    # Execute the test
    await run_test_sequence(apb_master, sequence)
```

## Advanced Integration

```python
from CocoTBFramework.tbclasses.apb.apb_command_handler import APBCommandHandler
from CocoTBFramework.components.memory_model import MemoryModel

@cocotb.test()
async def test_apb_slave(dut):
    # Create memory model
    memory = MemoryModel(size=4096, bytes_per_line=4, log=dut._log)
    
    # Create command handler
    cmd_handler = APBCommandHandler(dut, memory, log=dut._log)
    
    # Start the command handler
    await cmd_handler.start()
    
    # Run test
    # ...
    
    # Stop the command handler
    await cmd_handler.stop()
```

## See Also

- [APB Components](../../components/apb/index.md) - APB verification components
- [APB Scoreboard](../../scoreboards/apb_scoreboard.md) - Transaction verification for APB
- [WaveDrom APB](../wavedrom_user/apb.md) - WaveDrom visualization for APB

## Navigation

[↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
