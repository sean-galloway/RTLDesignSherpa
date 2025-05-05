# APB

## Overview

The `apb` module provides APB (AMBA Peripheral Bus) protocol-specific scenarios, checks, and signal groups for WaveDrom visualization. It extends the core WaveDrom utilities to facilitate protocol-specific verification and debugging of APB interfaces.

## Features

- Predefined APB signal groups for organized waveform display
- Protocol-specific verification scenarios for APB operation
- Custom debug checks for APB protocol violations
- FSM state transition validation
- Clock gating behavior verification
- Signal auto-detection for DUT compatibility

## Signal Groups

### APB_GROUPS

A dictionary defining APB-specific signal groupings for waveform display.

```python
APB_GROUPS = {
    "APB Interface": ["s_apb_PSEL", "s_apb_PENABLE", "s_apb_PREADY", "s_apb_PWRITE", 
                      "s_apb_PWDATA", "s_apb_PRDATA", "s_apb_PSLVERR"],
    "Control": ["pclk", "presetn", "cg_pclk", "o_apb_clock_gating", "r_wakeup"],
    "Command Channel": ["o_cmd_valid", "i_cmd_ready", "o_cmd_pwrite", "o_cmd_pwdata"],
    "Response Channel": ["i_rsp_valid", "o_rsp_ready", "i_rsp_prdata", "i_rsp_pslverr"],
    "State Machine": ["r_apb_state"]
}
```

### APB State Definitions

Constants defining APB FSM states and valid transitions.

```python
# Define valid APB FSM state transitions
APB_STATE_TRANSITIONS = {
    1: [2],     # IDLE(1) -> BUSY(2)
    2: [4],     # BUSY(2) -> WAIT(4) 
    4: [1]      # WAIT(4) -> IDLE(1)
}

# Define APB state values
APB_STATES = {
    1: "IDLE",
    2: "BUSY",
    4: "WAIT"
}
```

## Debug Check Functions

### check_apb_pready_timing

Checks if PREADY is properly asserted after cmd_valid and rsp_valid.

```python
async def check_apb_pready_timing(dut, wave_gen)
```

- Detects when the APB interface is stuck in BUSY state without response for an extended period

### check_command_response_handshake

Checks for improper command-response handshake.

```python
async def check_command_response_handshake(dut, wave_gen)
```

- Detects when command channel is stalled with valid signal asserted without ready

### check_clock_gating_behavior

Checks for proper clock gating behavior.

```python
async def check_clock_gating_behavior(dut, wave_gen)
```

- Verifies clock gating is active during idle periods
- Detects incorrect clock gating during active operations

### check_apb_protocol_violations

Comprehensive check for APB protocol violations.

```python
async def check_apb_protocol_violations(dut, wave_gen)
```

- Detects PENABLE without PSEL (protocol violation)
- Checks PSEL->PENABLE timing (must be on next cycle)
- Monitors PREADY responsiveness
- Checks for multiple PSEL/PENABLE during active transfer

### check_fsm_transitions

Monitors FSM state transitions for correctness.

```python
async def check_fsm_transitions(dut, wave_gen)
```

- Verifies state transitions follow the valid APB state machine flow
- Detects invalid state transitions

### check_fifo_overrun

Checks for potential FIFO overruns in command or response paths.

```python
async def check_fifo_overrun(dut, wave_gen)
```

- Monitors FIFO count signals approaching capacity

## Predefined APB Scenarios

### apb_setup_scenario

Scenario for verifying APB setup phase timing.

```python
apb_setup_scenario = ScenarioConfig(
    name="APB Transaction Setup",
    description="Verify APB setup phase timing",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # PSEL & PENABLE activates command valid
        SignalRelation(...),
        # PSEL & PENABLE leads to command valid
        SignalRelation(...),
        # Command valid leads to state transition to BUSY
        SignalRelation(...)
    ],
    debug_checks=[{
        'function': check_command_response_handshake,
        'description': "Check command handshake"
    }]
)
```

### apb_response_scenario

Scenario for verifying APB response phase timing.

```python
apb_response_scenario = ScenarioConfig(
    name="APB Response Handling",
    description="Verify APB response phase timing",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Response valid triggers PREADY
        SignalRelation(...),
        # PREADY leads to FSM transitioning to WAIT
        SignalRelation(...),
        # WAIT state always returns to IDLE
        SignalRelation(...)
    ],
    debug_checks=[{
        'function': check_apb_pready_timing,
        'description': "Check PREADY timing"
    }]
)
```

### apb_clock_gating_scenario

Scenario for verifying APB clock gating behavior.

```python
apb_clock_gating_scenario = ScenarioConfig(
    name="Clock Gating Behavior",
    description="Verify APB clock gating activation/deactivation",
    pre_cycles=3,
    post_cycles=3,
    relations=[
        # Activity wakes up the clock
        SignalRelation(...),
        # Wakeup disables clock gating
        SignalRelation(...)
    ],
    debug_checks=[{
        'function': check_clock_gating_behavior,
        'description': "Check clock gating behavior"
    }]
)
```

### apb_protocol_scenario

Scenario for verifying APB protocol compliance.

```python
apb_protocol_scenario = ScenarioConfig(
    name="APB Protocol Compliance",
    description="Verify APB protocol compliance",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # PSEL must precede PENABLE
        SignalRelation(...)
    ],
    debug_checks=[{
        'function': check_apb_protocol_violations,
        'description': "Check APB protocol violations"
    }]
)
```

### apb_state_machine_scenario

Scenario for verifying APB state machine transitions.

```python
apb_state_machine_scenario = ScenarioConfig(
    name="APB State Machine",
    description="Verify APB state machine transitions",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # IDLE to BUSY
        SignalRelation(...),
        # BUSY to WAIT
        SignalRelation(...),
        # WAIT to IDLE
        SignalRelation(...)
    ],
    debug_checks=[{
        'function': check_fsm_transitions,
        'description': "Check FSM transitions"
    }]
)
```

## Utility Functions

### get_signal_groups

Returns signal groups appropriate for the DUT.

```python
def get_signal_groups(dut):
    """
    Return signal groups appropriate for the DUT
    
    Args:
        dut: Device under test
        
    Returns:
        Dictionary of signal groups
    """
```

- Dynamically detects which APB signals are available in the DUT
- Creates appropriate signal groups based on available signals
- Falls back to predefined groups if no signals are found

### create_apb_scenarios

Creates APB scenarios based on available signals in the DUT.

```python
def create_apb_scenarios(dut, include_scenarios=None):
    """
    Create APB scenarios based on available signals in the DUT
    
    Args:
        dut: Device under test
        include_scenarios: Optional list of scenario names to include
                          (None = all available)
    
    Returns:
        List of applicable scenarios
    """
```

- Checks which signals are available in the DUT
- Includes only scenarios that are applicable based on available signals
- Optionally filters scenarios based on the include_scenarios parameter

## Example Usage

### Basic APB Waveform Generation

```python
from CocoTBFramework.tbclasses.wavedrom_user import apb
from CocoTBFramework.components.wavedrom_utils import WaveformContainer

@cocotb.test()
async def test_apb_interface(dut):
    # Get APB signal groups for this DUT
    signal_groups = apb.get_signal_groups(dut)
    
    # Create applicable APB scenarios
    scenarios = apb.create_apb_scenarios(dut)
    
    # Create waveform container
    container = WaveformContainer(
        title="APB Interface Verification",
        clock_signal="pclk",
        signal_groups=signal_groups,
        scenarios=scenarios
    )
    
    # Run all scenarios
    await container.run_all_scenarios(dut)
    
    # Generate WaveDrom output
    container.generate_wavedrom("apb_verification.json")
```

### Selective Scenario Verification

```python
# Create only specific APB scenarios
scenarios = apb.create_apb_scenarios(
    dut, 
    include_scenarios=["protocol", "state_machine"]
)
```

## APB Protocol Background

The AMBA APB (Advanced Peripheral Bus) is a simple, low-throughput peripheral bus specification designed for communication with peripherals that don't require high bandwidth. Key characteristics include:

1. **Phased Operation**: Uses setup and access phases for transfers
2. **Simple Control Signals**: PSEL, PENABLE, PWRITE
3. **Basic Handshaking**: PREADY for transfer completion
4. **Error Indication**: PSLVERR for error conditions
5. **Low Bandwidth**: Appropriate for low-speed peripherals

The standard APB state machine follows a simple flow:
- IDLE → SETUP → ACCESS → IDLE

In the implementation represented by this module, the states are:
- IDLE (1) → BUSY (2) → WAIT (4) → IDLE (1)

## Implementation Notes

- The module automatically adapts to the signal naming in the DUT
- Signal names often follow the pattern "s_apb_PREADY" for slave-side APB signals
- Debug checks can handle missing signals gracefully
- The implementation supports optional clock gating features
- Command and response channels represent the interface to internal logic

## See Also

- [APB Components](../../components/apb/index.md) - APB protocol components for CocoTB
- [APB Command Handler](../apb/apb_command_handler.md) - APB command handling

## Navigation

[↑ WaveDrom User Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
