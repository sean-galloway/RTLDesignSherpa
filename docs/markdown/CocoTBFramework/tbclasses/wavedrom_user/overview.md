# WaveDrom User Overview

## Introduction

The `wavedrom_user` module serves as a bridge between the core WaveDrom utilities and protocol-specific verification needs. While the core WaveDrom utilities provide the fundamental framework for waveform generation, the user modules extend this functionality with protocol-specific knowledge, making it easier to visualize and debug industry-standard bus protocols.

## Module Structure

Each protocol module in the `wavedrom_user` package follows a consistent structure:

1. **Signal Groups**: Predefined groupings of protocol-specific signals
2. **Debug Checks**: Protocol-specific verification functions
3. **Scenarios**: Predefined verification scenarios for common protocol operations
4. **Helper Functions**: Utilities for signal detection and scenario creation

## Available Protocols

### APB (AMBA Peripheral Bus)

The APB module provides utilities for visualizing and verifying the AMBA Peripheral Bus protocol, a simple, low-bandwidth address/data protocol suitable for peripheral devices.

Key features:
- Setup and access phase verification
- Protocol timing compliance checks
- Clock gating behavior verification
- FSM state transition validation

### AXI4 (AMBA Advanced eXtensible Interface 4)

The AXI4 module supports the high-performance, high-frequency AMBA AXI4 protocol, with separate address and data channels for reads and writes.

Key features:
- Channel-specific verification scenarios
- Burst transaction validation
- Handshake timing checks
- Interleaved transaction support
- Exclusive access verification

### FIFO (First-In-First-Out)

The FIFO module provides utilities for visualizing and verifying FIFO buffer interfaces, common in data buffering applications.

Key features:
- Overflow and underflow detection
- Fill level monitoring
- Support for both flop and mux-based implementations
- Data stability verification

### GAXI (Generic AXI)

The GAXI module supports a simplified version of the AXI protocol, often used for custom interfaces or simplified bus transfers.

Key features:
- Handshake protocol verification
- Multiple buffer implementation modes
- Backpressure behavior analysis
- Buffer fullness monitoring

## Integration with Test Environment

The `wavedrom_user` modules are designed to integrate seamlessly with CocoTB test environments:

```python
@cocotb.test()
async def test_protocol(dut):
    # Import protocol module
    from CocoTBFramework.tbclasses.wavedrom_user import apb
    from CocoTBFramework.components.wavedrom_utils import WaveformContainer
    
    # Get signal groups and scenarios for this specific DUT
    signal_groups = apb.get_signal_groups(dut)
    scenarios = apb.create_apb_scenarios(dut)
    
    # Create container
    container = WaveformContainer(
        title="Protocol Verification",
        clock_signal="clk",
        signal_groups=signal_groups,
        scenarios=scenarios
    )
    
    # Run verification
    await container.run_all_scenarios(dut)
    
    # Generate output
    container.generate_wavedrom("output.json")
```

## Advanced Usage

### Selective Scenario Creation

You can selectively create specific scenarios based on your verification needs:

```python
# Create only read and handshake scenarios for AXI4
from CocoTBFramework.tbclasses.wavedrom_user import axi4

scenarios = axi4.create_axi4_scenarios(
    dut, 
    include_scenarios=["read", "handshake"]
)
```

### Custom Signal Groups

While predefined signal groups are provided, you can customize them:

```python
from CocoTBFramework.tbclasses.wavedrom_user import fifo
from CocoTBFramework.components.wavedrom_utils import CommonGroups

# Get base FIFO groups
fifo_groups = fifo.get_signal_groups(dut)

# Combine with custom groups
custom_groups = CommonGroups.combine(
    fifo_groups,
    {"Debug": ["debug_count", "debug_state"]}
)
```

### Integration with Capture Module

For long-running simulations, integrate with the capture module:

```python
from CocoTBFramework.tbclasses.wavedrom_user import gaxi
from CocoTBFramework.components.wavedrom_utils.capture import (
    WaveformCapture, CaptureMode, create_standard_capture
)

# Create container
container = WaveformContainer(
    title="GAXI Verification",
    clock_signal="clk",
    signal_groups=gaxi.get_signal_groups(dut),
    scenarios=gaxi.create_gaxi_scenarios(dut, mode="skid")
)

# Create and start capture
capture = create_standard_capture(dut, container)
await capture.start_capture(CaptureMode.TRIGGER_BASED, 
                         trigger=SignalEvent("error", EdgeType.RISING))

# Run test...

# Stop capture
await capture.stop_capture()
```

## Best Practices

1. **Automatic Signal Detection**: Use the `get_signal_groups` function to automatically detect available signals in your DUT

2. **Selective Scenario Creation**: Only include scenarios relevant to your current test focus

3. **Protocol Combination**: For complex designs with multiple protocols, combine scenarios from different modules:

```python
# For an APB-to-AXI bridge
apb_scenarios = apb.create_apb_scenarios(dut)
axi_scenarios = axi4.create_axi4_scenarios(dut)
combined_scenarios = apb_scenarios + axi_scenarios
```

4. **Dynamic Configuration**: Pass appropriate parameters to scenario creation functions based on your specific DUT configuration

5. **Integration with Protocol Components**: Use alongside protocol-specific driver and monitor components for comprehensive verification

## Implementation Notes

- The modules automatically detect which signals are available in the DUT
- Scenarios are only created if the required signals are present
- Debug checks gracefully handle missing signals
- Default values are provided for common parameters
- The modules support various protocol configurations and implementations

## See Also

- [WaveDrom Utilities](../../components/wavedrom_utils/index.md) - Core WaveDrom utility components
- [Protocol Components](../../components/index.md) - Protocol-specific drivers and monitors
- [Scoreboards](../../scoreboards/index.md) - Protocol verification scoreboards

## Navigation

[↑ WaveDrom User Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
