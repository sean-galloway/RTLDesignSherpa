# WaveDrom User

## Overview

The `wavedrom_user` module extends the core WaveDrom utilities with protocol-specific implementations for common bus protocols used in digital design. These protocol-specific utilities make it easier to visualize and debug protocol interactions during CocoTB simulations.

## Key Features

- Protocol-specific signal groups for common bus protocols
- Pre-defined verification scenarios tailored to each protocol
- Custom debug checks for protocol-specific violations
- Easy integration with CocoTB test environments
- Automatic detection of available signals in the design under test
- Configurable verification scenarios based on design features

## Protocol Modules

- [APB](apb.md) - AMBA Peripheral Bus protocol utilities
- [AXI4](axi4.md) - AMBA Advanced eXtensible Interface 4 protocol utilities
- [FIFO](fifo.md) - FIFO buffer interface protocol utilities
- [GAXI](gaxi.md) - Generic AXI interface protocol utilities

## Usage Guide

- [Overview](overview.md) - Introduction and usage guidelines

## Basic Usage

```python
from CocoTBFramework.tbclasses.wavedrom_user import apb

@cocotb.test()
async def test_apb_protocol(dut):
    # Get APB signal groups for this DUT
    signal_groups = apb.get_signal_groups(dut)
    
    # Create APB verification scenarios
    apb_scenarios = apb.create_apb_scenarios(dut)
    
    # Create waveform container with APB scenarios
    container = WaveformContainer(
        title="APB Protocol Verification",
        clock_signal="pclk",
        signal_groups=signal_groups,
        scenarios=apb_scenarios
    )
    
    # Run verification
    await container.run_all_scenarios(dut)
    
    # Generate waveform
    container.generate_wavedrom("apb_verification.json")
```

## Advanced Integration

The protocol modules can be integrated with other CocoTBFramework components:

```python
from CocoTBFramework.tbclasses.wavedrom_user import axi4
from CocoTBFramework.components.wavedrom_utils.capture import (
    WaveformCapture, CaptureMode, create_standard_capture
)

@cocotb.test()
async def test_axi4_with_capture(dut):
    # Get AXI4 signal groups and scenarios
    signal_groups = axi4.get_signal_groups(dut)
    axi4_scenarios = axi4.create_axi4_scenarios(dut, ["read", "write"])
    
    # Create container
    container = WaveformContainer(
        title="AXI4 Protocol Verification",
        clock_signal="axi_aclk",
        signal_groups=signal_groups,
        scenarios=axi4_scenarios
    )
    
    # Create and start capture
    capture = create_standard_capture(dut, container)
    await capture.start_capture(CaptureMode.SCENARIO_BASED)
    
    # Run test
    # ...
    
    # Stop capture and generate output
    await capture.stop_capture()
    container.generate_wavedrom("axi4_verification.json")
```

## See Also

- [WaveDrom Utilities](../../components/wavedrom_utils/index.md) - Core WaveDrom utility components
- [APB Components](../../components/apb/index.md) - APB protocol components
- [AXI4 Components](../../components/axi4/index.md) - AXI4 protocol components

## Navigation

[↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
