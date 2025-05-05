# GAXI

## Overview

The `gaxi` module provides GAXI (Generic AXI) protocol-specific scenarios, checks, and signal groups for WaveDrom visualization. It extends the core WaveDrom utilities with specialized support for visualizing and debugging GAXI interfaces, which are simplified variants of the AXI protocol often used for internal interconnects.

## Features

- Predefined GAXI signal groups for standard and multi-signal modes
- Protocol-specific verification scenarios for different buffer implementations
- Support for multiple operational modes (skid, fifo_mux, fifo_flop)
- Custom debug checks for handshake stalls and buffer fullness
- Backpressure behavior analysis
- Automatic signal detection for DUT compatibility

## Signal Groups

### GAXI_GROUPS

A dictionary defining GAXI-specific signal groupings for waveform display.

```python
GAXI_GROUPS = {
    # Standard Mode (Single Bus)
    "GAXI Standard": [
        "m2s_valid", "s2m_ready", "m2s_pkt"
    ],
    # Multi-Signal Mode (Multiple Signals)
    "GAXI Multi": [
        "m2s_valid", "s2m_ready", "m2s_pkt_addr", "m2s_pkt_data", 
        "m2s_pkt_cmd", "m2s_pkt_strb"
    ],
    # Control Signals
    "Control": [
        "clk", "rst_n"
    ],
    # Buffer State
    "Buffer State": [
        "r_buffer_full", "r_buffer_empty", "r_buffer_count"
    ]
}
```

### GAXI_MODES

Defines the different operational modes for GAXI buffer implementations.

```python
GAXI_MODES = {
    "skid": {
        "description": "Standard skid buffer mode",
        "transfer_delay": 0  # Data transfers in same cycle when valid and ready are both high
    },
    "fifo_mux": {
        "description": "FIFO multiplexer mode with combinational output",
        "transfer_delay": 0  # Data appears in same cycle
    },
    "fifo_flop": {
        "description": "FIFO flip-flop mode with registered output",
        "transfer_delay": 1  # Data appears one cycle later
    }
}
```

## Debug Check Functions

### check_gaxi_handshake_stall

Checks for stalled valid without ready handshake.

```python
async def check_gaxi_handshake_stall(dut, wave_gen)
```

- Detects when valid is asserted without ready for too long
- Reports potential backpressure or stall conditions

### check_gaxi_ready_without_valid

Checks for ready without valid (potential inefficiency).

```python
async def check_gaxi_ready_without_valid(dut, wave_gen)
```

- Reports when ready is asserted for extended periods without valid
- Helps identify inefficient interface usage

### check_gaxi_buffer_fullness

Checks buffer fullness conditions.

```python
async def check_gaxi_buffer_fullness(dut, wave_gen)
```

- Monitors buffer fill level against capacity
- Warns when buffer is approaching full state
- Uses BUFFER_DEPTH parameter if available

### check_gaxi_data_transfer

Checks proper data transfer according to GAXI mode.

```python
async def check_gaxi_data_transfer(dut, wave_gen, mode="skid")
```

- Verifies data transfer timing based on specified mode
- Adapts to different buffer implementation characteristics
- Confirms data transfer on valid/ready handshake

### check_gaxi_backpressure

Checks for backpressure effects (ready deasserted after valid).

```python
async def check_gaxi_backpressure(dut, wave_gen)
```

- Detects when ready is deasserted while valid remains high
- Helps analyze backpressure propagation in the design

## Predefined GAXI Scenarios

### gaxi_handshake_scenario

Scenario for verifying GAXI handshaking behavior.

```python
gaxi_handshake_scenario = ScenarioConfig(
    name="GAXI Handshake Protocol",
    description="Verify GAXI handshaking behavior",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Valid leading to ready assertion
        SignalRelation(...),
        # Valid cleared after handshake
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': check_gaxi_handshake_stall,
            'description': "Check handshake stalls"
        },
        {
            'function': check_gaxi_ready_without_valid,
            'description': "Check ready without valid"
        }
    ]
)
```

### gaxi_skid_buffer_scenario

Scenario for verifying GAXI skid buffer mode operation.

```python
gaxi_skid_buffer_scenario = ScenarioConfig(
    name="GAXI Skid Buffer Mode",
    description="Verify GAXI skid buffer mode operation",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Valid & ready causing data transfer
        SignalRelation(...),
        # Buffer fullness affecting ready
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': check_gaxi_buffer_fullness,
            'description': "Check buffer fullness"
        },
        {
            'function': lambda dut, wave_gen: check_gaxi_data_transfer(dut, wave_gen, "skid"),
            'description': "Check data transfer (skid mode)"
        }
    ]
)
```

### gaxi_fifo_mux_scenario

Scenario for verifying GAXI FIFO mux mode operation.

```python
gaxi_fifo_mux_scenario = ScenarioConfig(
    name="GAXI FIFO Mux Mode",
    description="Verify GAXI FIFO mux mode operation",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Valid & ready causing data transfer
        SignalRelation(...),
        # Data changes immediately when valid & ready
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': lambda dut, wave_gen: check_gaxi_data_transfer(dut, wave_gen, "fifo_mux"),
            'description': "Check data transfer (fifo_mux mode)"
        },
        {
            'function': check_gaxi_backpressure,
            'description': "Check backpressure effects"
        }
    ]
)
```

### gaxi_fifo_flop_scenario

Scenario for verifying GAXI FIFO flop mode operation.

```python
gaxi_fifo_flop_scenario = ScenarioConfig(
    name="GAXI FIFO Flop Mode",
    description="Verify GAXI FIFO flop mode operation",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Valid & ready causing data transfer in next cycle
        SignalRelation(...),
        # Data changes one cycle after valid & ready
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': lambda dut, wave_gen: check_gaxi_data_transfer(dut, wave_gen, "fifo_flop"),
            'description': "Check data transfer (fifo_flop mode)"
        },
        {
            'function': check_gaxi_backpressure,
            'description': "Check backpressure effects"
        }
    ]
)
```

### gaxi_buffer_scenario

Scenario for verifying GAXI buffer state transitions.

```python
gaxi_buffer_scenario = ScenarioConfig(
    name="GAXI Buffer States",
    description="Verify GAXI buffer state transitions",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Handshakes affecting buffer count
        SignalRelation(...),
        # Buffer full affecting ready
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': check_gaxi_buffer_fullness,
            'description': "Check buffer fullness"
        }
    ]
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

- Dynamically detects which GAXI signals are available in the DUT
- Checks for both standard single-bus and multi-signal modes
- Creates appropriate signal groups based on available signals
- Falls back to predefined groups if no signals are found

### create_gaxi_scenarios

Creates GAXI scenarios based on available signals in the DUT and the specified operating mode.

```python
def create_gaxi_scenarios(dut, mode="skid", include_scenarios=None):
    """
    Create GAXI scenarios based on available signals in the DUT
    and the specified operating mode
    
    Args:
        dut: Device under test
        mode: GAXI mode ("skid", "fifo_mux", or "fifo_flop")
        include_scenarios: Optional list of scenario names to include
                          (None = all applicable)
    
    Returns:
        List of applicable scenarios
    """
```

- Checks which GAXI signals are available in the DUT
- Creates appropriate scenarios based on available signals and specified mode
- Supports different buffer implementation modes
- Optionally filters scenarios based on the include_scenarios parameter

## Example Usage

### Basic GAXI Waveform Generation

```python
from CocoTBFramework.tbclasses.wavedrom_user import gaxi
from CocoTBFramework.components.wavedrom_utils import WaveformContainer

@cocotb.test()
async def test_gaxi_interface(dut):
    # Get GAXI signal groups for this DUT
    signal_groups = gaxi.get_signal_groups(dut)
    
    # Create applicable GAXI scenarios
    scenarios = gaxi.create_gaxi_scenarios(dut, mode="skid")
    
    # Create waveform container
    container = WaveformContainer(
        title="GAXI Interface Verification",
        clock_signal="clk",
        signal_groups=signal_groups,
        scenarios=scenarios
    )
    
    # Run all scenarios
    await container.run_all_scenarios(dut)
    
    # Generate WaveDrom output
    container.generate_wavedrom("gaxi_verification.json")
```

### Selective Scenario Verification

```python
# Create only handshake and buffer scenarios
scenarios = gaxi.create_gaxi_scenarios(
    dut, 
    mode="fifo_flop",
    include_scenarios=["handshake", "buffer"]
)
```

### Specifying GAXI Mode

```python
# Create GAXI scenarios for fifo_mux mode
scenarios = gaxi.create_gaxi_scenarios(dut, mode="fifo_mux")
```

## GAXI Interface Background

GAXI (Generic AXI) is a simplified variant of the AXI protocol often used for internal interconnects when the full complexity of AXI is not required. Key characteristics include:

1. **Handshake Protocol**:
   - Valid/Ready handshake for flow control
   - Data transfers when both Valid and Ready are asserted

2. **Packet-Based Transfer**:
   - Single packet signal for standard mode (m2s_pkt)
   - Multiple signals for expanded mode (m2s_pkt_addr, m2s_pkt_data, etc.)

3. **Buffer Implementations**:
   - **Skid Buffer**: Single-stage buffer for handshake decoupling
   - **FIFO Mux**: Multi-stage buffer with combinational output
   - **FIFO Flop**: Multi-stage buffer with registered output

4. **Interface Signals**:
   - m2s_valid: Master-to-Slave valid signal
   - s2m_ready: Slave-to-Master ready signal
   - m2s_pkt: Data packet (standard mode)
   - m2s_pkt_* signals: Component signals (multi-signal mode)

5. **Buffer State Signals**:
   - r_buffer_full: Buffer full indicator
   - r_buffer_empty: Buffer empty indicator
   - r_buffer_count: Buffer occupancy counter

## Implementation Characteristics

### Skid Buffer Mode

- Single-stage buffer for handshake decoupling
- Data transfers in the same cycle when valid and ready are both high
- Primarily used for timing improvement and breaking combinational paths

### FIFO Mux Mode

- Multi-stage buffer with combinational output
- Data appears in the same cycle as the handshake
- Useful for deeper buffering with minimal latency

### FIFO Flop Mode

- Multi-stage buffer with registered output
- Data appears one cycle after the handshake
- Provides better timing characteristics at the cost of one cycle latency

## Implementation Notes

- The module automatically adapts to signal naming in the DUT
- Support for both single-bus and expanded multi-signal modes
- Debug checks handle missing signals gracefully
- Different buffer implementation modes are supported
- Buffer depth is detected from BUFFER_DEPTH parameter if available
- Backpressure behavior is properly analyzed

## Best Practices

1. **Handshake Protocol**: Always use valid/ready handshake for flow control
2. **Buffer Selection**: Choose appropriate buffer implementation based on latency/throughput requirements
3. **Backpressure Handling**: Ensure proper backpressure propagation through the interface
4. **Buffer Sizing**: Size buffers appropriately to prevent overflow conditions
5. **Mode Verification**: Verify data transfer timing based on the specific implementation mode
6. **Interface Efficiency**: Monitor for inefficient interface usage patterns

## See Also

- [GAXI Components](../../components/gaxi/index.md) - GAXI interface components for CocoTB
- [GAXI Scoreboard](../../scoreboards/gaxi_scoreboard.md) - GAXI transaction verification scoreboard

## Navigation

[↑ WaveDrom User Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
