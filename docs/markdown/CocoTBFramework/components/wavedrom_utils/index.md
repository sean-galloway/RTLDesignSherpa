# WaveDrom Utilities

## Overview

The WaveDrom Utilities provide a comprehensive framework for generating waveform diagrams directly from CocoTB simulations. These components allow for the visualization of signal relationships, protocol timing, and verification scenarios, making it easier to debug and document hardware designs.

## Key Features

- Integration with CocoTB simulation framework
- Automatic waveform generation from simulation data
- Visualization of signal relationships and protocol timing
- Support for multiple verification scenarios
- Customizable signal grouping and styling
- Annotations for timing violations and protocol errors
- Export to WaveDrom JSON format for rendering
- Protocol-specific verification checks
- Statistical analysis and pattern detection
- Efficient waveform capture management

## Components

### Core Components

- [Common Groups](common_groups.md) - Predefined signal groups for standard protocols
- [Container](container.md) - Scenario management and execution framework
- [Generator](generator.md) - Core waveform generation engine
- [Models](models.md) - Data models for signal events and relationships
- [Example Test](example_test.md) - Usage examples and demonstration code

### Advanced Components

- [Protocol Checks](protocol_checks.md) - Reusable verification checks for common protocols
- [Enhanced Generator](enhanced_generator.md) - Extended generator with advanced features
- [Capture](capture.md) - Utilities for managing waveform capture

## Guides and Examples

- [Overview](overview.md) - Introduction to WaveDrom utilities
- [Example Test](example_test.md) - Example usage in a CocoTB test

## Related Components

- [APB Components](../apb/index.md) - APB protocol implementation
- [AXI4 Components](../axi4/index.md) - AXI4 protocol implementation
- [FIFO Components](../fifo/index.md) - FIFO protocol implementation
- [GAXI Components](../gaxi/index.md) - GAXI protocol implementation

## Using WaveDrom Utilities

### Basic Usage

```python
from CocoTBFramework.components.wavedrom_utils import (
    EdgeType, ArrowStyle, SignalEvent, SignalRelation,
    WaveformContainer, ScenarioConfig, CommonGroups
)

# Define a verification scenario
scenario = ScenarioConfig(
    name="Protocol Timing Check",
    description="Verify request-acknowledge timing constraints",
    relations=[
        SignalRelation(
            cause=SignalEvent("req", EdgeType.RISING),
            effect=SignalEvent("ack", EdgeType.RISING),
            min_cycles=1,
            max_cycles=3,
            style=ArrowStyle.SETUP
        )
    ]
)

# Create a container with the scenario
container = WaveformContainer(
    title="Protocol Verification",
    clock_signal="clk",
    signal_groups=CommonGroups.combine(
        CommonGroups.CONTROL,
        CommonGroups.REQ_ACK
    ),
    scenarios=[scenario]
)

# Run the scenario and generate a waveform
await container.run_all_scenarios(dut)
container.generate_wavedrom("protocol_verification.json")
```

### Advanced Usage

```python
from CocoTBFramework.components.wavedrom_utils.protocol_checks import (
    ProtocolType, create_protocol_checks
)
from CocoTBFramework.components.wavedrom_utils.enhanced_generator import (
    EnhancedWaveDromGenerator, EnhancedWaveDromConfig
)
from CocoTBFramework.components.wavedrom_utils.capture import (
    WaveformCapture, CaptureMode, create_standard_capture
)

# Create protocol checks
protocol_checks = create_protocol_checks(
    ProtocolType.HANDSHAKE,
    valid_signal="valid",
    ready_signal="ready"
)

# Create a scenario with checks
scenario = ScenarioConfig(
    name="Handshake Protocol",
    description="Verify handshake protocol",
    relations=[...],
    debug_checks=list(protocol_checks.values())
)

# Create a container
container = WaveformContainer(
    title="Advanced Verification",
    clock_signal="clk",
    signal_groups=signal_groups,
    scenarios=[scenario]
)

# Create and start capture process
capture = create_standard_capture(dut, container)
await capture.start_capture()

# Run test and stop capture
# ...test code...
await capture.stop_capture()

# Generate enhanced output with statistics
config = EnhancedWaveDromConfig(
    statistical_analysis=True,
    include_html_wrapper=True
)
generator = EnhancedWaveDromGenerator(dut.clk, config)
# ... add signals and run ...
generator.generate("advanced_verification.html")
```

## Navigation

[↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
