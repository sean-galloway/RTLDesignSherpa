# Protocol Checks

## Overview

The `protocol_checks` module provides a comprehensive collection of reusable verification checks for common hardware protocol patterns and violations. These checks can be integrated with the WaveDrom generator to automatically detect and visualize protocol-specific issues during simulation.

## Features

- Standard checks for common protocol patterns
- Support for multiple protocol types (handshake, state machine, FIFO, etc.)
- Customizable timeout and threshold parameters
- Integration with WaveDrom debugging annotations
- Protocol check suite generation based on protocol type
- Support for both synchronous and asynchronous interfaces

## Classes

### ProtocolType

An enum class defining the types of protocols for check selection.

```python
class ProtocolType(Enum):
    """Types of protocols for check selection"""
    HANDSHAKE = auto()  # Basic valid/ready or req/ack handshake
    STATE_MACHINE = auto()  # State machine transitions
    CLOCK_GATING = auto()  # Clock gating control
    FIFO = auto()  # FIFO buffer checks
    MEMORY = auto()  # Memory interface
    APB = auto()  # APB protocol
    AXI = auto()  # AXI protocol
    SPI = auto()  # SPI protocol
    I2C = auto()  # I2C protocol
```

## Check Functions

### check_handshake_stall

Checks for handshake protocol stalls where valid is asserted without ready for too long.

```python
async def check_handshake_stall(dut, wave_gen, valid_signal="valid", ready_signal="ready", timeout=5)
```

- `dut`: Device under test
- `wave_gen`: WaveDrom generator instance
- `valid_signal`: Name of the valid signal
- `ready_signal`: Name of the ready signal
- `timeout`: Maximum cycles valid can be asserted without ready

### check_ready_without_valid

Checks for ready asserted without valid, which can be a protocol violation.

```python
async def check_ready_without_valid(dut, wave_gen, valid_signal="valid", ready_signal="ready")
```

- `dut`: Device under test
- `wave_gen`: WaveDrom generator instance
- `valid_signal`: Name of the valid signal
- `ready_signal`: Name of the ready signal

### check_state_deadlock

Checks for state machine deadlock where a state remains unchanged for too long.

```python
async def check_state_deadlock(dut, wave_gen, state_signal="state", timeout=10)
```

- `dut`: Device under test
- `wave_gen`: WaveDrom generator instance
- `state_signal`: Name of the state signal
- `timeout`: Maximum cycles in same state before considered deadlocked

### check_fifo_overflow

Checks for FIFO near-overflow conditions.

```python
async def check_fifo_overflow(dut, wave_gen, count_signal="count", capacity=8, threshold=0.8)
```

- `dut`: Device under test
- `wave_gen`: WaveDrom generator instance
- `count_signal`: Name of the FIFO count signal
- `capacity`: Maximum FIFO capacity
- `threshold`: Threshold percentage for warning (0.0-1.0)

### check_clock_gating

Checks for proper clock gating behavior.

```python
async def check_clock_gating(dut, wave_gen, state_signal="state", idle_state=1, 
                           clock_gate_signal="clock_gating", idle_count_signal=None)
```

- `dut`: Device under test
- `wave_gen`: WaveDrom generator instance
- `state_signal`: Name of the state signal
- `idle_state`: Value representing the idle state
- `clock_gate_signal`: Name of the clock gating control signal
- `idle_count_signal`: Optional signal indicating required idle cycles

### check_invalid_state_transition

Checks for invalid state machine transitions.

```python
async def check_invalid_state_transition(dut, wave_gen, state_signal="state", 
                                       valid_transitions=None)
```

- `dut`: Device under test
- `wave_gen`: WaveDrom generator instance
- `state_signal`: Name of the state signal
- `valid_transitions`: Dictionary mapping from states to valid next states

## Suite Generator Function

### create_protocol_checks

Creates a standard set of protocol checks for a specific protocol type.

```python
def create_protocol_checks(protocol_type: ProtocolType, **kwargs) -> Dict[str, Dict[str, Any]]
```

- `protocol_type`: Type of protocol to create checks for
- `**kwargs`: Protocol-specific configuration parameters

Returns:
- Dictionary of debug check configurations

## Example Usage

### Basic Handshake Protocol Checks

```python
from CocoTBFramework.components.wavedrom_utils.protocol_checks import (
    ProtocolType, create_protocol_checks
)

# Create handshake protocol checks
handshake_checks = create_protocol_checks(
    ProtocolType.HANDSHAKE,
    valid_signal="m_valid",
    ready_signal="s_ready",
    timeout=10
)

# Create a scenario with these checks
handshake_scenario = ScenarioConfig(
    name="Handshake Protocol",
    description="Check handshake protocol compliance",
    relations=[...],
    debug_checks=list(handshake_checks.values())
)
```

### State Machine Checks with Custom Transitions

```python
# Define valid state transitions
valid_transitions = {
    0: [1],          # IDLE can go to BUSY
    1: [2],          # BUSY can go to DONE
    2: [0]           # DONE can go to IDLE
}

# Create state machine checks
state_checks = create_protocol_checks(
    ProtocolType.STATE_MACHINE,
    state_signal="fsm_state",
    timeout=20,
    valid_transitions=valid_transitions
)

# Create a scenario with these checks
state_scenario = ScenarioConfig(
    name="State Machine Verification",
    description="Verify state machine behavior",
    relations=[...],
    debug_checks=list(state_checks.values())
)
```

### FIFO Overflow Detection

```python
# Create FIFO checks with custom thresholds
fifo_checks = create_protocol_checks(
    ProtocolType.FIFO,
    count_signal="fifo_count",
    capacity=16,
    threshold=0.9  # Warn when FIFO is 90% full
)

# Create a scenario with these checks
fifo_scenario = ScenarioConfig(
    name="FIFO Monitoring",
    description="Check for FIFO overflow conditions",
    relations=[...],
    debug_checks=list(fifo_checks.values())
)
```

### Clock Gating Verification

```python
# Create clock gating checks
clock_gating_checks = create_protocol_checks(
    ProtocolType.CLOCK_GATING,
    state_signal="curr_state",
    idle_state=0,  # 0 = IDLE state
    clock_gate_signal="clk_gate_en",
    idle_count_signal="idle_counter"
)

# Create a scenario with these checks
clock_gating_scenario = ScenarioConfig(
    name="Clock Gating Behavior",
    description="Verify proper clock gating",
    relations=[...],
    debug_checks=list(clock_gating_checks.values())
)
```

## Protocol-Specific Checks

The module provides predefined check suites for common protocol types:

### Handshake Protocol

For valid/ready or request/acknowledge protocols:
- Checks for valid without ready (stall)
- Checks for ready without valid (potential violation)

### State Machine 

For sequential logic state machines:
- Checks for deadlocks (state unchanged for too long)
- Validates state transitions against allowed transitions

### FIFO

For FIFO buffer implementations:
- Monitors fill level against capacity
- Warns when approaching overflow thresholds

### Clock Gating

For clock-gated designs:
- Verifies gating activates after appropriate idle time
- Checks for incorrect gating during active states

## Implementation Notes

- All check functions return `True` if an issue is detected, `False` otherwise
- Issues are recorded as debug annotations in the wave generator
- Check functions gracefully handle missing signals by skipping checks
- Integer values with `integer` property (from cocotb) are properly handled

## Best Practices

1. **Configure Timeouts**: Adjust timeout values based on your design's expected behavior
2. **Signal Naming**: Ensure signal names match exactly what's in your DUT
3. **Combine Checks**: Use multiple check types for comprehensive verification
4. **Handle Exceptions**: The checks handle most exceptions internally, but consider adding your own error handling
5. **Customize Parameters**: Adjust thresholds and parameters for your specific design requirements

## See Also

- [Generator](generator.md) - WaveDrom generator for creating waveform diagrams
- [Models](models.md) - Data models for signal events and relationships
- [Container](container.md) - Container for managing verification scenarios
- [Capture](capture.md) - Utilities for managing waveform capture

## Navigation

[↑ WaveDrom Utils Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
