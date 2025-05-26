# Generator

## Overview

The `WaveDromGenerator` class is the core engine for capturing signal values during simulation and generating WaveDrom-compatible JSON output. It handles signal sampling, edge detection, relationship processing, and formatting of waveform data.

## Features

- Automated signal sampling during CocoTB simulation
- Edge detection for rising, falling, and value changes
- Relationship tracking between signal events
- Debug annotation support for protocol violations
- Generation of WaveDrom-compatible JSON output
- Statistics tracking for signal events

## Classes

### WaveDromGenerator

The main class for generating WaveDrom diagrams from CocoTB simulations.

#### Constructor

```python
def __init__(self, clock):
    """
    Initialize the WaveDrom generator with a clock signal

    Args:
        clock: Clock signal from DUT
    """
```

#### Attributes

- `clock`: Clock signal for synchronization
- `signals`: Dictionary of tracked signals and their values
- `relations`: List of signal relationships to monitor
- `detected_relations`: List of detected signal relationships
- `current_cycle`: Current simulation cycle
- `event_history`: List of detected signal events
- `debug_points`: List of manually added debug annotations

#### Key Methods

```python
def add_signal(self, name: str, dut_path: str):
    """
    Add a signal to track during simulation

    Args:
        name: Display name for the signal
        dut_path: Path to signal in DUT hierarchy
    """
```

```python
def add_relation(self, relation: SignalRelation):
    """
    Add a timing relationship between signals

    Args:
        relation: SignalRelation object defining the relationship
    """
```

```python
async def sample(self):
    """Sample all signals and check for relationships"""
```

```python
def add_debug_point(self, cycle: int, message: str, signals: Dict[str, Any]):
    """
    Add a debugging annotation

    Args:
        cycle: Clock cycle for the annotation
        message: Debug message
        signals: Dict of signal values at this debug point
    """
```

```python
def get_last_value(self, signal_name: str) -> Any:
    """
    Get the last recorded value of a signal

    Args:
        signal_name: Name of the signal

    Returns:
        Last recorded value
    """
```

```python
def cycles_since_event(self, event: SignalEvent) -> int:
    """
    Calculate cycles since a specific event

    Args:
        event: The event to check

    Returns:
        Number of cycles since last occurrence, or -1 if not found
    """
```

```python
def generate(self, output_file: Optional[str] = None) -> Dict:
    """
    Generate WaveDrom JSON output

    Args:
        output_file: Optional path to save JSON output

    Returns:
        WaveDrom JSON configuration dictionary
    """
```

## Example Usage

### Basic Signal Tracking

```python
from CocoTBFramework.components.wavedrom_utils import WaveDromGenerator

@cocotb.test()
async def test_waveform_generation(dut):
    # Create generator
    generator = WaveDromGenerator(dut.clk)
    
    # Add signals to track
    generator.add_signal("clk", "clk")
    generator.add_signal("reset", "rst_n")
    generator.add_signal("data", "data")
    generator.add_signal("valid", "valid")
    generator.add_signal("ready", "ready")
    
    # Run simulation and sample signals
    for _ in range(20):
        await generator.sample()
        
    # Generate WaveDrom output
    wavedrom_json = generator.generate("output.json")
```

### Tracking Signal Relationships

```python
from CocoTBFramework.components.wavedrom_utils import (
    WaveDromGenerator, SignalEvent, SignalRelation, EdgeType, ArrowStyle
)

@cocotb.test()
async def test_protocol_timing(dut):
    # Create generator
    generator = WaveDromGenerator(dut.clk)
    
    # Add signals to track
    generator.add_signal("clk", "clk")
    generator.add_signal("valid", "valid")
    generator.add_signal("ready", "ready")
    generator.add_signal("data", "data")
    
    # Add relationship to track
    generator.add_relation(SignalRelation(
        cause=SignalEvent("valid", EdgeType.RISING),
        effect=SignalEvent("ready", EdgeType.RISING),
        min_cycles=1,
        max_cycles=3,
        style=ArrowStyle.SPLINE
    ))
    
    # Run simulation
    for _ in range(20):
        await generator.sample()
        
    # Check detected relationships
    for relation in generator.detected_relations:
        print(f"Detected relation: {relation.cause.signal} -> {relation.effect.signal}")
        for cause_cycle, effect_cycle in relation.detected_pairs:
            print(f"  At cycles: {cause_cycle} -> {effect_cycle}")
    
    # Generate WaveDrom output
    wavedrom_json = generator.generate("protocol_timing.json")
```

### Adding Debug Annotations

```python
@cocotb.test()
async def test_protocol_violations(dut):
    # Create generator
    generator = WaveDromGenerator(dut.clk)
    
    # Add signals to track
    generator.add_signal("clk", "clk")
    generator.add_signal("valid", "valid")
    generator.add_signal("ready", "ready")
    
    # Simulate and check for violations
    for cycle in range(20):
        await generator.sample()
        
        # Check for a ready without valid condition
        if dut.ready.value == 1 and dut.valid.value == 0:
            generator.add_debug_point(
                generator.current_cycle,
                "Protocol violation: ready asserted without valid",
                {'valid': 0, 'ready': 1}
            )
    
    # Generate WaveDrom output with annotations
    wavedrom_json = generator.generate("protocol_violations.json")
```

## Tracking Signal Values

The generator tracks signal values and events throughout the simulation:

1. **Value Collection**: Each signal's value is sampled at every clock cycle
2. **Edge Detection**: Rising and falling edges are detected and recorded
3. **Event History**: A comprehensive history of all events is maintained
4. **Relationship Detection**: Signal relationships are checked against events

## Wave String Generation

The generator converts collected signal values into WaveDrom-compatible wave strings:

```
Signal: 0 0 1 1 1 0 0 0 1 1 0
Wave:   0...1...0...1.0
```

This format efficiently represents signal values with transitions indicated by new characters and continuations represented by dots.

## WaveDrom JSON Structure

The generated JSON has the following structure:

```json
{
  "signal": [
    {"name": "clk", "wave": "p...."},
    {"name": "data", "wave": "x.345x", "data": ["D1", "D2", "D3", "D4"]},
    {"name": "valid", "wave": "0.1..0"}
  ],
  "edge": [
    {"from": "valid", "to": "ready", "time": 2, "style": "->"},
    {"text": "Protocol violation", "time": 4}
  ],
  "config": {"hscale": 1},
  "groups": [
    {"name": "Control", "signals": ["clk", "reset"]},
    {"name": "Data", "signals": ["data", "valid", "ready"]}
  ]
}
```

This structure includes:
- Signal definitions with names and wave patterns
- Edge definitions showing relationships
- Text annotations for debug points
- Configuration options
- Signal grouping information

## Best Practices

1. **Efficient Sampling**: Only sample at necessary clock edges
2. **Signal Organization**: Add signals in logical groups
3. **Path Specification**: Use correct DUT signal paths
4. **Relationship Definition**: Set appropriate min_cycles and max_cycles
5. **Debug Annotations**: Add clear and specific debug messages
6. **Output Format**: Use JSON output for further processing
7. **Edge Detection**: Be aware of the different edge types (RISING, FALLING, ANY_CHANGE)

## Implementation Details

### Edge Detection

The generator detects the following edge types:

- `EdgeType.RISING`: 0 to 1 transition
- `EdgeType.FALLING`: 1 to 0 transition
- `EdgeType.ANY_CHANGE`: Any value change
- `EdgeType.BOTH`: Both rising and falling edges (special case)

### Relationship Processing

Relationships are processed as follows:

1. Scan the event history for matching cause events
2. Scan the event history for matching effect events
3. Match cause-effect pairs based on timing constraints
4. Store detected pairs in the relationship object

## See Also

- [Models](models.md) - Signal event and relationship models
- [Container](container.md) - High-level scenario management
- [Common Groups](common_groups.md) - Predefined signal groups
- [Example Test](example_test.md) - Complete usage examples

## Navigation

[↑ WaveDrom Utils Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
