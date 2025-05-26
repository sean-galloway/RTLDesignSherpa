# Models

## Overview

The `models` module defines the core data structures used for WaveDrom generation, including edge types, arrow styles, signal events, and timing relationships. These models provide the foundation for expressing complex signal interactions and protocol timing requirements.

## Features

- Enum definitions for edge types and arrow styles
- Dataclasses for signal events and relationships
- Support for various event types (edges, state changes, patterns)
- Customizable timing constraints and visual styles
- Factory methods for common event patterns

## Classes

### EdgeType

An enum class defining the types of signal edges to detect.

```python
class EdgeType(Enum):
    """Types of signal edges to detect"""
    RISING = auto()      # Low to high transition
    FALLING = auto()     # High to low transition
    BOTH = auto()        # Either rising or falling edge
    ANY_CHANGE = auto()  # Any value change
```

### ArrowStyle

An enum class defining WaveDrom arrow styles with visual examples.

```python
class ArrowStyle(Enum):
    """WaveDrom arrow styles with visual examples"""
    STRAIGHT = "->"       # A ──→ B    Direct causation
    SPLINE = "~>"         # A ～→ B    Indirect/delayed effect
    BLOCKING = "|=>"      # A ═→ B    Blocking assignment
    NONBLOCKING = "|~>"   # A ═~→ B   Non-blocking assignment
    SETUP = "-|>"         # A ─|→ B   Setup time requirement
    HOLD = "|->"          # A |─→ B   Hold time requirement
    DOUBLE = "->>"        # A ─→→ B   Strong causation
    ASYNC = "~>>"         # A ～→→ B  Asynchronous effect
    WEAK = "-->"          # A ──→ B   Weak dependency
    BIDIRECTIONAL = "<->" # A ←─→ B   Bidirectional relationship
```

### SignalEvent

A dataclass representing a signal event like an edge or value change.

#### Constructor

```python
@dataclass
class SignalEvent:
    signal: str                                 # Signal name
    edge_type: EdgeType                         # Type of edge
    value: Optional[Union[int, str, dict]] = None  # Optional value
    cycle_offset: int = 0                       # Cycle offset
```

#### Attributes

- `signal`: Name of the signal
- `edge_type`: Type of edge to detect
- `value`: Optional value to match (for state changes or specific values)
- `cycle_offset`: Optional cycle offset for timing calculations

#### Static Methods

```python
@staticmethod
def state_change(signal: str, from_state: str, to_state: str):
    """Create event for state machine transition"""
```

```python
@staticmethod
def counter_value(signal: str, value: int):
    """Create event for counter reaching specific value"""
```

```python
@staticmethod
def pattern_match(signal: str, pattern: dict):
    """Create event for matching a signal pattern"""
```

### SignalRelation

A dataclass defining a relationship between signal events.

#### Constructor

```python
@dataclass
class SignalRelation:
    cause: SignalEvent                          # Cause event
    effect: SignalEvent                         # Effect event
    min_cycles: int = 1                         # Minimum cycles between cause and effect
    max_cycles: Optional[int] = None            # Maximum cycles between cause and effect
    style: ArrowStyle = ArrowStyle.SPLINE       # Arrow style for visualization
    debug_info: Optional[dict] = None           # Debug metadata
    detected_pairs: List[tuple] = field(default_factory=list)  # Detected event pairs
```

#### Attributes

- `cause`: The event that triggers the relationship
- `effect`: The event that should follow the cause
- `min_cycles`: Minimum number of clock cycles between cause and effect
- `max_cycles`: Maximum number of clock cycles between cause and effect (None for unlimited)
- `style`: Arrow style for WaveDrom visualization
- `debug_info`: Optional dictionary for debugging metadata
- `detected_pairs`: List of detected cause-effect cycle pairs

## Example Usage

### Basic Edge Detection

```python
from CocoTBFramework.components.wavedrom_utils.models import (
    EdgeType, SignalEvent, SignalRelation, ArrowStyle
)

# Define a rising edge event
reset_deassert = SignalEvent("reset_n", EdgeType.RISING)

# Define a falling edge event
valid_assert = SignalEvent("valid", EdgeType.FALLING)

# Define an any-change event
data_change = SignalEvent("data", EdgeType.ANY_CHANGE)
```

### State Machine Transitions

```python
# Define a state transition event
state_transition = SignalEvent.state_change(
    signal="state",
    from_state="IDLE",
    to_state="BUSY"
)

# Check for state transition followed by done signal
state_done_relation = SignalRelation(
    cause=state_transition,
    effect=SignalEvent("done", EdgeType.RISING),
    min_cycles=2,
    max_cycles=5,
    style=ArrowStyle.STRAIGHT
)
```

### Protocol Timing Requirements

```python
# Define setup time relationship
setup_relation = SignalRelation(
    cause=SignalEvent("addr_valid", EdgeType.RISING),
    effect=SignalEvent("clk", EdgeType.RISING),
    min_cycles=2,  # 2 cycles setup time
    style=ArrowStyle.SETUP
)

# Define hold time relationship
hold_relation = SignalRelation(
    cause=SignalEvent("clk", EdgeType.RISING),
    effect=SignalEvent("addr_valid", EdgeType.FALLING),
    min_cycles=1,  # 1 cycle hold time
    style=ArrowStyle.HOLD
)
```

### Counter Threshold Detection

```python
# Define an event for counter reaching a specific value
counter_event = SignalEvent.counter_value("count", 10)

# Define a relationship for counter threshold followed by done
counter_relation = SignalRelation(
    cause=counter_event,
    effect=SignalEvent("done", EdgeType.RISING),
    min_cycles=1,
    max_cycles=3,
    style=ArrowStyle.SPLINE
)
```

### Pattern Matching

```python
# Define a pattern match event
error_pattern = SignalEvent.pattern_match(
    "status",
    {"error_flag": 1, "overflow": 1}
)

# Define a relationship for error pattern followed by reset
error_relation = SignalRelation(
    cause=error_pattern,
    effect=SignalEvent("reset", EdgeType.FALLING),
    min_cycles=1,
    max_cycles=5,
    style=ArrowStyle.ASYNC
)
```

## Arrow Style Applications

Different arrow styles are useful for representing various types of relationships:

| Arrow Style | Usage | Example |
|-------------|-------|---------|
| STRAIGHT    | Direct causation | Write enable → Data valid |
| SPLINE      | Delayed or indirect effect | Request → Response |
| BLOCKING    | Synchronous assignment | Assignment in synchronous logic |
| NONBLOCKING | Non-blocking assignment | Non-blocking assignment in HDL |
| SETUP       | Setup time requirement | Data stable → Clock edge |
| HOLD        | Hold time requirement | Clock edge → Data change |
| DOUBLE      | Strong causation | Master → Slave in hierarchy |
| ASYNC       | Asynchronous effect | Interrupt → Handler |
| WEAK        | Weak dependency | Optional feature activation |
| BIDIRECTIONAL | Two-way relationship | Handshake signals |

## Edge Type Applications

Each edge type is useful for specific verification scenarios:

| Edge Type | Usage | Example |
|-----------|-------|---------|
| RISING    | Low to high transition | Enable signal assertion |
| FALLING   | High to low transition | Reset signal deassertion |
| BOTH      | Any edge transition | Clock edge detection |
| ANY_CHANGE| Any value change | Data bus value changes |

## Best Practices

1. **Clear Naming**: Use descriptive signal names for better readability
2. **Appropriate Edge Types**: Choose the correct edge type for each signal
3. **Reasonable Timing**: Set realistic min_cycles and max_cycles values
4. **Meaningful Styles**: Select arrow styles that reflect the relationship type
5. **Specific Values**: Use value matching for specific state or data conditions
6. **Factory Methods**: Use the static factory methods for specialized events
7. **Debug Info**: Include debug_info for complex relationships

## Implementation Details

The classes in this module are primarily dataclasses, providing simple data structures without complex behavior. The actual detection and processing of events and relationships is handled by the `WaveDromGenerator` class.

## See Also

- [Generator](generator.md) - Uses these models to detect events
- [Container](container.md) - High-level management of scenarios
- [Example Test](example_test.md) - Complete usage examples

## Navigation

[↑ WaveDrom Utils Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
