# Example Test

## Overview

The `example_test.py` module provides a comprehensive demonstration of using the WaveDrom utilities within a CocoTB test environment. It showcases the creation of verification scenarios, defining signal relationships, implementing custom debug checks, and generating WaveDrom diagrams.

## Features

- Complete working example of WaveDrom utility usage
- Protocol timing verification scenario
- State machine deadlock detection scenario
- Custom debug check functions
- Signal group configuration
- Integration with CocoTB test flow

## Debug Check Functions

### check_protocol_timing

A function that checks for req-ack protocol timing violations.

```python
async def check_protocol_timing(dut, wave_gen):
    """Check for req-ack protocol violations"""
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
```

This function:
1. Checks if the request signal is high and acknowledge is low
2. Determines how many cycles have passed since the request was asserted
3. If more than 3 cycles have passed, adds a debug point and returns True

### check_state_deadlock

A function that checks for state machine deadlocks.

```python
async def check_state_deadlock(dut, wave_gen):
    """Check for state machine deadlocks"""
    stuck_cycles = wave_gen.cycles_since_event(
        SignalEvent("state", EdgeType.ANY_CHANGE)
    )
    if stuck_cycles > 10:
        wave_gen.add_debug_point(
            wave_gen.current_cycle,
            f"State machine stuck in {dut.state.value} for {stuck_cycles} cycles",
            {'state': dut.state.value, 'stuck_cycles': stuck_cycles}
        )
        return True
    return False
```

This function:
1. Determines how many cycles have passed since the state signal last changed
2. If more than 10 cycles have passed, adds a debug point and returns True

## Verification Scenarios

### Protocol Timing Scenario

A scenario for verifying request-acknowledge timing constraints.

```python
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
    debug_checks=[{
        'function': check_protocol_timing,
        'description': "Check req-ack timing"
    }]
)
```

This scenario:
1. Defines a relationship between request and acknowledge signals
2. Specifies that acknowledge should assert 1-3 cycles after request
3. Includes a debug check for protocol timing violations

### State Machine Deadlock Scenario

A scenario for detecting potential state machine deadlocks.

```python
state_scenario = ScenarioConfig(
    name="State Machine Deadlock",
    description="Detect potential state machine deadlocks",
    pre_cycles=5,
    post_cycles=2,
    relations=[
        SignalRelation(
            cause=SignalEvent.state_change("state", "BUSY", "DONE"),
            effect=SignalEvent("done", EdgeType.RISING),
            style=ArrowStyle.STRAIGHT
        )
    ],
    debug_checks=[{
        'function': check_state_deadlock,
        'description': "Check for stuck states"
    }]
)
```

This scenario:
1. Defines a relationship between a state transition and the done signal
2. Includes a debug check for state machine deadlocks

## CocoTB Test Function

The main test function that demonstrates the WaveDrom utilities.

```python
@cocotb.test()
async def test_protocol_verification(dut):
    """Test protocol behaviors with waveform verification"""

    # Clock generation
    clock = dut.clk
    cocotb.start_soon(generate_clock(dut))

    # Reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1

    # Use predefined signal groups and add custom ones
    signal_groups = CommonGroups.combine(
        CommonGroups.CONTROL,
        CommonGroups.REQ_ACK,
        CommonGroups.custom("Status", ["done", "error"]),
        {"State": ["state", "counter"]}
    )

    # Create container with scenarios
    container = WaveformContainer(
        title="Protocol Verification",
        clock_signal="clk",
        signal_groups=signal_groups,
        scenarios=[
            protocol_scenario,
            state_scenario
        ]
    )

    # Run all scenarios
    await container.run_all_scenarios(dut)

    # Generate final waveform
    container.generate_wavedrom("protocol_verification.json")
```

This test function:
1. Sets up clock generation and reset sequence
2. Creates signal groups using predefined and custom groups
3. Creates a waveform container with both scenarios
4. Runs all scenarios sequentially
5. Generates the final WaveDrom JSON output

## Clock Generation

A helper function for generating the clock signal.

```python
async def generate_clock(dut):
    """Generate clock signal"""
    while True:
        dut.clk.value = 0
        await Timer(5, units='ns')
        dut.clk.value = 1
        await Timer(5, units='ns')
```

This function:
1. Toggles the clock signal between 0 and 1
2. Waits 5 ns between each transition
3. Runs continuously in the background

## Complete Example

The complete example demonstrates how to:
1. Define debug check functions for protocol verification
2. Create verification scenarios with relationships and debug checks
3. Set up signal groups for the waveform display
4. Create and configure a waveform container
5. Run verification scenarios in a CocoTB test
6. Generate WaveDrom JSON output

## Generated WaveDrom Output

The final output is a WaveDrom JSON file that can be rendered as an SVG diagram. The diagram includes:

1. Signal waveforms for all tracked signals
2. Arrow annotations showing detected relationships
3. Text annotations for detected protocol violations
4. Signal groups for organized display

## Extending the Example

This example can be extended in several ways:

1. **Additional Protocols**: Define new scenarios for other protocols
2. **Complex State Machines**: Add more complex state transition relationships
3. **Data Path Verification**: Track data values along with control signals
4. **Performance Metrics**: Add debug checks for performance measurements
5. **Multiple Interfaces**: Track signals from multiple interfaces simultaneously

## Best Practices

1. **Organize Signals**: Use CommonGroups to organize related signals
2. **Clear Scenarios**: Create separate scenarios for different verification aspects
3. **Focused Debug Checks**: Write specific debug checks for critical protocol rules
4. **Reusable Functions**: Define reusable debug check functions
5. **Appropriate Relations**: Define relationships with clear timing constraints
6. **Standard Patterns**: Use standard patterns for common protocols
7. **Descriptive Names**: Use descriptive names for scenarios and debug checks

## See Also

- [Models](models.md) - Signal event and relationship models
- [Generator](generator.md) - WaveDrom generation engine
- [Container](container.md) - Scenario management
- [Common Groups](common_groups.md) - Predefined signal groups

## Navigation

[↑ WaveDrom Utils Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
