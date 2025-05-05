# WaveDrom Utilities Overview

## Introduction

The WaveDrom Utilities provide a powerful framework for generating waveform diagrams directly from CocoTB simulations. These utilities bridge the gap between simulation and documentation, allowing engineers to visualize signal interactions, protocol timing, and verification scenarios in a standardized format.

## What is WaveDrom?

WaveDrom is a free and open-source digital timing diagram rendering engine that generates SVG images from a JSON-based description. It is commonly used in hardware documentation to represent signals and their relationships over time. The JSON format is human-readable and can be easily generated programmatically.

The CocoTBFramework WaveDrom Utilities extend this capability by automatically generating WaveDrom JSON from simulation data, allowing for dynamic waveform generation that accurately represents the actual behavior of a design under test.

## Architecture

The WaveDrom Utilities now consist of an expanded set of components working together:

```
┌─────────────────────┐
│ Verification Test   │
└─────────┬───────────┘
          │
┌─────────▼───────────┐
│    WaveformCapture  │
│                     │
│  ┌───────────────┐  │
│  │WaveformContainer│ │
│  │                │ │
│  │ ┌────────────┐ │ │
│  │ │ScenarioConfig│ │ │
│  │ └────────┬───┘ │ │
│  │          │     │ │
│  │ ┌────────▼───┐ │ │
│  │ │ WaveDromGen │◄┼─┼────┐
│  │ └────────┬───┘ │ │    │
│  │          │     │ │    │
│  │ ┌────────▼───┐ │ │    │
│  │ │SignalEvents │ │ │    │
│  │ └────────────┘ │ │    │
│  └───────────────┘  │    │
└─────────────────────┘    │
          │                │
┌─────────▼────────┐       │
│  Protocol Checks │───────┘
└─────────────────┬┘
          │
┌─────────▼────────┐
│  WaveDrom JSON   │
└─────────────────┬┘
          │
┌─────────▼────────┐
│ Enhanced Output  │
└─────────────────┬┘
```

1. **Models** (`models.py`): Defines the core data structures for events, relationships, and styling
2. **Generator** (`generator.py`): Samples signals during simulation and generates WaveDrom JSON
3. **Container** (`container.py`): Manages verification scenarios and overall test execution
4. **Common Groups** (`common_groups.py`): Provides predefined signal groupings for standard protocols
5. **Protocol Checks** (`protocol_checks.py`): Reusable verification checks for common protocols
6. **Enhanced Generator** (`enhanced_generator.py`): Extended generator with advanced features
7. **Capture** (`capture.py`): Manages the waveform capture process
8. **Example Test** (`example_test.py`): Demonstrates usage in a CocoTB test environment

## Key Concepts

### Signal Events

Signal events represent changes in signal values, such as rising or falling edges. They are the fundamental building blocks for creating relationships and timing annotations.

```python
# Example of a signal event definition
event = SignalEvent("clock", EdgeType.RISING)
```

### Signal Relationships

Relationships define timing dependencies between signal events, such as setup time, hold time, or causal relationships.

```python
# Example of a signal relationship
relation = SignalRelation(
    cause=SignalEvent("req", EdgeType.RISING),
    effect=SignalEvent("ack", EdgeType.RISING),
    min_cycles=1,
    max_cycles=3,
    style=ArrowStyle.SETUP
)
```

### Verification Scenarios

Scenarios group related signal events and relationships to verify specific aspects of a design's behavior.

```python
# Example of a verification scenario
scenario = ScenarioConfig(
    name="Protocol Timing Check",
    description="Verify request-acknowledge timing constraints",
    relations=[relation],
    debug_checks=[check_function]
)
```

### Protocol Checks

Protocol checks are reusable verification functions that detect common protocol violations or issues.

```python
# Example of protocol checks
handshake_checks = create_protocol_checks(
    ProtocolType.HANDSHAKE,
    valid_signal="valid",
    ready_signal="ready",
    timeout=5
)
```

### Enhanced Visualization

The enhanced generator provides additional visualization capabilities, including statistics and pattern detection.

```python
# Example of enhanced visualization
config = EnhancedWaveDromConfig(
    statistical_analysis=True,
    include_html_wrapper=True
)
generator = EnhancedWaveDromGenerator(dut.clk, config)
```

### Waveform Capture

The capture module manages the process of sampling and storing waveform data during simulation.

```python
# Example of waveform capture
capture = create_standard_capture(dut, container)
await capture.start_capture(CaptureMode.CONTINUOUS)
```

## Workflow

The typical workflow for using the WaveDrom Utilities involves:

1. **Setup**: Define signal events, relationships, scenarios, and protocol checks
2. **Configuration**: Configure the capture process and generator options
3. **Execution**: Run the simulation while capturing waveform data
4. **Analysis**: Process the collected data to identify timing violations or protocol errors
5. **Visualization**: Generate standard or enhanced WaveDrom output

```python
# Basic workflow example
container = WaveformContainer(
    title="Protocol Verification",
    clock_signal="clk",
    signal_groups=signal_groups,
    scenarios=[scenario1, scenario2]
)

capture = create_standard_capture(dut, container)
await capture.start_capture()

# Run test...

await capture.stop_capture()
container.generate_wavedrom("output.json")
```

## Use Cases

The WaveDrom Utilities are particularly useful for:

### Protocol Verification

Verify that signal interactions follow protocol specifications, with visual indicators of timing violations.

```
      ┌───┐   ┌───┐   ┌───┐   ┌───┐   ┌───┐
Clk   │   └───┘   └───┘   └───┘   └───┘   
      │
      │       ┌───────────────┐
Req   │_______│               │___________
      │       │               │
      │           ┌───────────────┐
Ack   │___________|               │_______
      │           │               │
      ▲           ▲
      │           │
      └───────────┘
        Setup time
```

### State Machine Analysis

Track state transitions and identify potential deadlocks or illegal state sequences.

```
         ┌───┐   ┌───┐   ┌───┐   ┌───┐
Clk      │   └───┘   └───┘   └───┘   
         │
State    │ IDLE │ BUSY │ PROC │ DONE 
         │
         │               ┌─────┐
Done     │_______________|     │_______
         │               │     │
```

### Signal Relationship Documentation

Document causal relationships between signals for better understanding of design behavior.

```
         ┌───┐   ┌───┐   ┌───┐   ┌───┐
Clk      │   └───┘   └───┘   └───┘   
         │
         │       ┌───────┐
Write    │_______|       │_____________
         │       │       │
         │               ┌───────┐
WrDone   │_______________|       │_____
         │               │       │
         │       ↓       │
         │       └───────┼───────→
         │               │
```

### Pattern Detection and Statistics

Analyze signal patterns and collect statistics for performance analysis.

```
Signal: data
Patterns detected: 10101010 (4 occurrences), 11110000 (2 occurrences)
Toggle rate: 0.43 toggles/cycle
Time high: 62.5%
```

## Advanced Features

### Protocol Checks

The protocol checks module provides reusable verification functions for common protocol patterns:

- **Handshake Protocols**: Check for stalls, protocol violations
- **State Machines**: Verify proper transitions, detect deadlocks
- **FIFOs**: Monitor for overflow/underflow conditions
- **Clock Gating**: Ensure proper clock gating behavior

### Enhanced Visualization

The enhanced generator provides additional visualization capabilities:

- **Signal Statistics**: Toggle rates, time high/low percentages
- **Pattern Detection**: Find specific bit patterns in signals
- **HTML Output**: Interactive visualization with statistics tables
- **Custom Annotations**: Add detailed annotations to waveforms

### Efficient Capture

The capture module provides efficient management of the capture process:

- **Multiple Modes**: Continuous, time-window, trigger-based, scenario-based
- **Resource Management**: Prevent memory issues in long simulations
- **Pause/Resume**: Control capture during specific test sections
- **Performance Monitoring**: Track capture efficiency

## Example Usage

The `example_test.py` file provides a complete example of using the WaveDrom Utilities within a CocoTB test:

```python
@cocotb.test()
async def test_protocol_verification(dut):
    # Clock generation
    cocotb.start_soon(generate_clock(dut))
    
    # Create protocol checks
    handshake_checks = create_protocol_checks(
        ProtocolType.HANDSHAKE,
        valid_signal="valid",
        ready_signal="ready"
    )
    
    # Create a scenario with protocol checks
    scenario = ScenarioConfig(
        name="Protocol Verification",
        description="Verify handshake protocol",
        relations=[...],
        debug_checks=list(handshake_checks.values())
    )
    
    # Create container with scenario
    container = WaveformContainer(
        title="Protocol Verification",
        clock_signal="clk",
        signal_groups=signal_groups,
        scenarios=[scenario]
    )
    
    # Create and start capture
    capture = create_standard_capture(dut, container)
    await capture.start_capture()
    
    # Run test...
    
    # Stop capture
    await capture.stop_capture()
    
    # Generate enhanced output
    config = EnhancedWaveDromConfig(
        statistical_analysis=True,
        include_html_wrapper=True
    )
    generator = EnhancedWaveDromGenerator(dut.clk, config)
    # ... add signals ...
    generator.generate("protocol_verification.html")
```

## Best Practices

1. **Organize Signals**: Use signal groups to organize related signals
2. **Define Relationships Clearly**: Specify both the cause and effect events for each relationship
3. **Set Realistic Timing**: Use appropriate min_cycles and max_cycles values
4. **Add Protocol Checks**: Include standard checks for common protocol violations
5. **Use Enhanced Generator**: Use the enhanced generator for more detailed analysis
6. **Configure Capture**: Select the appropriate capture mode for your test
7. **Manage Resources**: Set appropriate limits for long-running simulations

## Navigation

[↑ WaveDrom Utils Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
