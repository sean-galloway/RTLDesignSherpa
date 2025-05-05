# FIFO

## Overview

The `fifo` module provides FIFO (First-In-First-Out) buffer interface-specific scenarios, checks, and signal groups for WaveDrom visualization. It extends the core WaveDrom utilities with specialized support for visualizing and debugging FIFO interfaces commonly used in digital designs for data buffering.

## Features

- Predefined FIFO signal groups for write and read interfaces
- Protocol-specific verification scenarios for FIFO operations
- Support for different FIFO operational modes (flop and mux)
- Custom debug checks for overflow, underflow, and fullness conditions
- Data stability verification
- Automatic signal detection for DUT compatibility

## Signal Groups

### FIFO_GROUPS

A dictionary defining FIFO-specific signal groupings for waveform display.

```python
FIFO_GROUPS = {
    # Write Interface
    "FIFO Write": [
        "i_write", "o_wr_full", "o_wr_almost_full", "o_wr_count",
        "i_wr_data"
    ],
    # Read Interface
    "FIFO Read": [
        "i_read", "o_rd_empty", "o_rd_almost_empty", "o_rd_count",
        "o_rd_data", "ow_rd_data"
    ],
    # Control Signals
    "Control": [
        "clk", "rst_n"
    ],
    # Internal State
    "Internal State": [
        "r_write_ptr", "r_read_ptr", "r_count"
    ]
}
```

### FIFO_MODES

Defines the different operational modes for FIFO read data output.

```python
FIFO_MODES = {
    "flop": {
        "description": "Registered read data (flop mode)",
        "data_signal": "o_rd_data",
        "data_delay": 1  # Data appears 1 cycle after read
    },
    "mux": {
        "description": "Combinational read data (mux mode)",
        "data_signal": "ow_rd_data",
        "data_delay": 0  # Data appears same cycle as read
    }
}
```

## Debug Check Functions

### check_fifo_overflow

Checks for FIFO overflow condition.

```python
async def check_fifo_overflow(dut, wave_gen)
```

- Detects write operations while the FIFO is full
- Reports protocol violations that could lead to data loss

### check_fifo_underflow

Checks for FIFO underflow condition.

```python
async def check_fifo_underflow(dut, wave_gen)
```

- Detects read operations while the FIFO is empty
- Reports protocol violations that could lead to invalid data reads

### check_fifo_fullness_warning

Checks for FIFO approaching full condition.

```python
async def check_fifo_fullness_warning(dut, wave_gen)
```

- Monitors FIFO fill level against a percentage threshold
- Provides warnings when FIFO is nearing capacity
- Uses FIFO_DEPTH parameter if available

### check_fifo_emptiness_warning

Checks for FIFO approaching empty condition.

```python
async def check_fifo_emptiness_warning(dut, wave_gen)
```

- Warns when FIFO entries are low during active read operations
- Helps detect potential underflow before it occurs

### check_fifo_simultaneous_read_write

Checks for simultaneous read and write behavior.

```python
async def check_fifo_simultaneous_read_write(dut, wave_gen)
```

- Monitors count stability during simultaneous read/write operations
- Useful for verifying correct implementation of simultaneous access

### check_fifo_data_stability

Checks for data stability during read operations.

```python
async def check_fifo_data_stability(dut, wave_gen, mode="flop")
```

- Verifies data stability based on FIFO mode (flop or mux)
- Ensures data is valid at the appropriate time after read signal

## Predefined FIFO Scenarios

### fifo_write_scenario

Scenario for verifying FIFO write interface behavior.

```python
fifo_write_scenario = ScenarioConfig(
    name="FIFO Write Operations",
    description="Verify FIFO write interface behavior",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Write causing count to increase
        SignalRelation(...),
        # Write affecting full status (when approaching capacity)
        SignalRelation(...),
        # Full status blocking writes
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': check_fifo_overflow,
            'description': "Check overflow condition"
        },
        {
            'function': check_fifo_fullness_warning,
            'description': "Check fullness warning"
        }
    ]
)
```

### fifo_read_flop_scenario

Scenario for verifying FIFO read interface behavior with registered data.

```python
fifo_read_flop_scenario = ScenarioConfig(
    name="FIFO Read Operations (Flop Mode)",
    description="Verify FIFO read interface behavior with registered data",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Read causing count to decrease
        SignalRelation(...),
        # Read triggering data output after 1 cycle (registered)
        SignalRelation(...),
        # Empty status blocking reads
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': check_fifo_underflow,
            'description': "Check underflow condition"
        },
        {
            'function': check_fifo_emptiness_warning,
            'description': "Check emptiness warning"
        },
        {
            'function': lambda dut, wave_gen: check_fifo_data_stability(dut, wave_gen, "flop"),
            'description': "Check data stability (flop mode)"
        }
    ]
)
```

### fifo_read_mux_scenario

Scenario for verifying FIFO read interface behavior with combinational data.

```python
fifo_read_mux_scenario = ScenarioConfig(
    name="FIFO Read Operations (Mux Mode)",
    description="Verify FIFO read interface behavior with combinational data",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Read causing count to decrease
        SignalRelation(...),
        # Read immediately presenting data (combinational)
        SignalRelation(...),
        # Empty status blocking reads
        SignalRelation(...)
    ],
    debug_checks=[...]
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

- Dynamically detects which FIFO signals are available in the DUT
- Creates appropriate signal groups based on available signals
- Organizes signals by functional group (write interface, read interface, etc.)
- Falls back to predefined groups if no signals are found

### create_fifo_scenarios

Creates FIFO scenarios based on available signals in the DUT.

```python
def create_fifo_scenarios(dut, mode="flop", include_scenarios=None):
    """
    Create FIFO scenarios based on available signals in the DUT
    
    Args:
        dut: Device under test
        mode: FIFO read data mode ("flop" or "mux")
        include_scenarios: Optional list of scenario names to include
                          (None = all available)
    
    Returns:
        List of applicable scenarios
    """
```

- Checks which FIFO interface signals are available in the DUT
- Creates appropriate scenarios based on available signals
- Selects appropriate read mode scenario based on mode parameter
- Optionally filters scenarios based on the include_scenarios parameter

## Example Usage

### Basic FIFO Waveform Generation

```python
from CocoTBFramework.tbclasses.wavedrom_user import fifo
from CocoTBFramework.components.wavedrom_utils import WaveformContainer

@cocotb.test()
async def test_fifo_interface(dut):
    # Get FIFO signal groups for this DUT
    signal_groups = fifo.get_signal_groups(dut)
    
    # Create applicable FIFO scenarios
    scenarios = fifo.create_fifo_scenarios(dut, mode="flop")
    
    # Create waveform container
    container = WaveformContainer(
        title="FIFO Interface Verification",
        clock_signal="clk",
        signal_groups=signal_groups,
        scenarios=scenarios
    )
    
    # Run all scenarios
    await container.run_all_scenarios(dut)
    
    # Generate WaveDrom output
    container.generate_wavedrom("fifo_verification.json")
```

### Selective Scenario Verification

```python
# Create only write scenario
scenarios = fifo.create_fifo_scenarios(
    dut, 
    include_scenarios=["write"]
)
```

### Specifying FIFO Mode

```python
# Create FIFO scenarios for mux mode
scenarios = fifo.create_fifo_scenarios(dut, mode="mux")
```

## FIFO Interface Background

FIFOs (First-In-First-Out) are fundamental data buffer components used in digital designs for various purposes:

1. **Data Buffering**: Temporary storage between modules with different data rates
2. **Clock Domain Crossing**: Transferring data between different clock domains
3. **Flow Control**: Managing data flow by providing backpressure when full
4. **Protocol Adaptation**: Adapting between different interface protocols

Key characteristics of FIFO interfaces include:

1. **Write Interface**:
   - Write control signal (i_write)
   - Full status indicator (o_wr_full)
   - Almost full indicator for early warning (o_wr_almost_full)
   - Fill level counter (o_wr_count)
   - Write data input (i_wr_data)

2. **Read Interface**:
   - Read control signal (i_read)
   - Empty status indicator (o_rd_empty)
   - Almost empty indicator for early warning (o_rd_almost_empty)
   - Fill level counter (o_rd_count)
   - Read data output (o_rd_data or ow_rd_data)

3. **Read Data Modes**:
   - **Flop Mode**: Registered output with 1-cycle delay (o_rd_data)
   - **Mux Mode**: Combinational output with 0-cycle delay (ow_rd_data)

4. **Internal State**:
   - Write pointer (r_write_ptr)
   - Read pointer (r_read_ptr)
   - Entry counter (r_count)

## Implementation Notes

- The module automatically adapts to signal naming in the DUT
- Debug checks handle missing signals gracefully
- Different read data timing modes are supported (flop vs. mux)
- The implementation detects FIFO_DEPTH parameter if available
- Simultaneous read/write operations are properly verified
- Data stability checks adapt to the FIFO read data mode

## Best Practices

1. **Overflow Prevention**: Always check write full status before writing
2. **Underflow Prevention**: Always check read empty status before reading
3. **Status Monitoring**: Use almost_full/almost_empty for early warning
4. **Proper Mode Selection**: Choose flop or mux mode based on timing requirements
5. **Simultaneous Operations**: Verify correct behavior when read and write occur simultaneously
6. **Reset Behavior**: Ensure proper reset behavior (pointers and count cleared)

## See Also

- [FIFO Components](../../components/fifo/index.md) - FIFO interface components for CocoTB
- [FIFO Scoreboard](../../scoreboards/fifo_scoreboard.md) - FIFO transaction verification scoreboard

## Navigation

[↑ WaveDrom User Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
