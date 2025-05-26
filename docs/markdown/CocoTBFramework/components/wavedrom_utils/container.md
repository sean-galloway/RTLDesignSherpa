# Container

## Overview

The `WaveformContainer` class provides a high-level framework for managing and executing multiple verification scenarios in a CocoTB environment. It orchestrates the collection of waveform data and generation of WaveDrom diagrams, making it easier to visualize and document complex protocol interactions.

## Features

- Management of multiple verification scenarios in a single test
- Automatic signal sampling during simulation
- Detection and visualization of signal relationships
- Support for custom debug checks during simulation
- Export to WaveDrom JSON format for rendering
- Comprehensive scenario configuration and execution

## Classes

### ScenarioConfig

A dataclass that defines a verification scenario with timing relationships and debug checks.

#### Constructor

```python
@dataclass
class ScenarioConfig:
    name: str                                   # Scenario name
    description: str                            # Scenario description
    pre_cycles: int = 2                         # Cycles to capture before first event
    post_cycles: int = 2                        # Cycles to capture after last event
    relations: List[SignalRelation] = field(default_factory=list)  # Signal relationships
    debug_checks: List[Dict[str, Any]] = field(default_factory=list)  # Debug checks
```

#### Attributes

- `name`: String identifier for the scenario
- `description`: Human-readable description of the scenario
- `pre_cycles`: Number of cycles to capture before the first event
- `post_cycles`: Number of cycles to capture after the last event
- `relations`: List of `SignalRelation` objects defining timing relationships
- `debug_checks`: List of debug check functions to run during simulation

### WaveformContainer

A container for managing multiple verification scenarios and generating waveform diagrams.

#### Constructor

```python
@dataclass
class WaveformContainer:
    title: str                                 # Container title
    clock_signal: str                          # Clock signal name
    signal_groups: Dict[str, List[str]]        # Signal groupings
    scenarios: List[ScenarioConfig]            # Verification scenarios
```

#### Attributes

- `title`: Title for the waveform diagram
- `clock_signal`: Name of the clock signal to use for synchronization
- `signal_groups`: Dictionary mapping group names to lists of signal names
- `scenarios`: List of `ScenarioConfig` objects defining verification scenarios
- `wave_gen`: Internal `WaveDromGenerator` instance created during initialization

#### Key Methods

```python
async def run_scenario(self, dut, scenario: ScenarioConfig)
```
- Runs a specific verification scenario
- Args:
  - `dut`: CocoTB device under test
  - `scenario`: Scenario configuration to run

```python
async def run_all_scenarios(self, dut)
```
- Runs all scenarios in sequence
- Args:
  - `dut`: CocoTB device under test

```python
def generate_wavedrom(self, output_file: Optional[str] = None) -> Dict
```
- Generates WaveDrom JSON with all scenarios
- Args:
  - `output_file`: Optional file to write JSON output
- Returns:
  - WaveDrom JSON configuration object

## Example Usage

### Basic Container Setup

```python
from CocoTBFramework.components.wavedrom_utils import (
    EdgeType, ArrowStyle, SignalEvent, SignalRelation,
    WaveformContainer, ScenarioConfig, CommonGroups
)

# Define a verification scenario
protocol_scenario = ScenarioConfig(
    name="Protocol Timing Check",
    description="Verify request-acknowledge timing constraints",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        SignalRelation(
            cause=SignalEvent("req", EdgeType.RISING),
            effect=SignalEvent("ack", EdgeType.RISING),
            min_cycles=1,
            max_cycles=3,
            style=ArrowStyle.SETUP
        )
    ],
    debug_checks=[]
)

# Create signal groups
signal_groups = CommonGroups.combine(
    CommonGroups.CONTROL,
    CommonGroups.REQ_ACK
)

# Create container
container = WaveformContainer(
    title="Protocol Verification",
    clock_signal="clk",
    signal_groups=signal_groups,
    scenarios=[protocol_scenario]
)
```

### Running Scenarios

```python
@cocotb.test()
async def test_protocol_verification(dut):
    # Clock generation
    cocotb.start_soon(generate_clock(dut))
    
    # Reset sequence
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    
    # Run verification scenarios
    await container.run_all_scenarios(dut)
    
    # Generate waveform
    container.generate_wavedrom("protocol_verification.json")
```

### Adding Debug Checks

```python
# Define a debug check function
async def check_protocol_timing(dut, wave_gen):
    if dut.req.value == 1 and dut.ack.value == 0:
        cycles_since_req = wave_gen.cycles_since_event(
            SignalEvent("req", EdgeType.RISING)
        )
        if cycles_since_req > 3:
            wave_gen.add_debug_point(
                wave_gen.current_cycle,
                "Protocol violation: ACK not received within 3 cycles",
                {'req': 1, 'ack': 0, 'cycles': cycles_since_req}
            )
            return True
    return False

# Create scenario with debug check
scenario = ScenarioConfig(
    name="Protocol Timing",
    description="Check for request-acknowledge timing violations",
    relations=[...],
    debug_checks=[{
        'function': check_protocol_timing,
        'description': "Check req-ack timing"
    }]
)
```

## Debug Checks

Debug checks are custom functions that run during simulation to detect protocol violations or other conditions that might not be captured by simple signal relationships. They have the following signature:

```python
async def check_function(dut, wave_gen):
    # Check for conditions
    if violation_detected:
        wave_gen.add_debug_point(
            wave_gen.current_cycle,
            "Description of violation",
            {'signal1': value1, 'signal2': value2}
        )
        return True  # Indicate event detected
    return False     # No event detected
```

When a debug check returns `True`, it's considered an event for the purpose of determining when to stop capturing cycles for the scenario.

## Implementation Details

### Scenario Execution Flow

The container executes each scenario using the following flow:

1. Add all signal relations to the wave generator
2. Begin sampling signals for the specified pre-cycles
3. Continue sampling until all expected events are detected
4. Capture additional post-cycles after the last event
5. Move to the next scenario

### Event Detection

The container tracks two types of events:

1. **Relation Events**: Detected when a signal relationship's cause and effect are observed
2. **Debug Events**: Detected when a debug check function returns `True`

These events are used to determine when to stop capturing cycles for a scenario.

## Best Practices

1. **Organize Scenarios**: Create separate scenarios for different aspects of protocol verification
2. **Set Appropriate Cycles**: Configure pre_cycles and post_cycles to provide adequate context
3. **Use Debug Checks**: Include custom debug checks for complex protocol violations
4. **Group Related Signals**: Use CommonGroups to organize signals logically
5. **Provide Clear Descriptions**: Use descriptive names and descriptions for scenarios
6. **Set a Safety Limit**: The container includes a 1000-cycle safety limit to prevent infinite loops

## See Also

- [Generator](generator.md) - Used by the container to generate waveforms
- [Models](models.md) - Signal event and relationship models
- [Common Groups](common_groups.md) - Predefined signal groups
- [Example Test](example_test.md) - Complete usage example

## Navigation

[↑ WaveDrom Utils Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
