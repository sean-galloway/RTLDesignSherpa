# AXI4

## Overview

The `axi4` module provides AXI4 (AMBA Advanced eXtensible Interface 4) protocol-specific scenarios, checks, and signal groups for WaveDrom visualization. It extends the core WaveDrom utilities with specialized support for visualizing and debugging AXI4 bus interfaces.

## Features

- Predefined AXI4 signal groups for all five channels
- Protocol-specific verification scenarios for read/write operations
- Custom debug checks for AXI4 protocol violations
- Burst transaction validation
- Exclusive access verification
- Handshake timing analysis
- Automatic signal detection for DUT compatibility

## Signal Groups

### AXI4_GROUPS

A dictionary defining AXI4-specific signal groupings for waveform display.

```python
AXI4_GROUPS = {
    # Write Address Channel
    "AXI Write Address": [
        "axi_awvalid", "axi_awready", "axi_awid", "axi_awaddr", 
        "axi_awlen", "axi_awsize", "axi_awburst", "axi_awlock",
        "axi_awcache", "axi_awprot", "axi_awqos", "axi_awregion", "axi_awuser"
    ],
    # Write Data Channel
    "AXI Write Data": [
        "axi_wvalid", "axi_wready", "axi_wdata", "axi_wstrb", 
        "axi_wlast", "axi_wuser"
    ],
    # Write Response Channel
    "AXI Write Response": [
        "axi_bvalid", "axi_bready", "axi_bid", "axi_bresp", "axi_buser"
    ],
    # Read Address Channel
    "AXI Read Address": [
        "axi_arvalid", "axi_arready", "axi_arid", "axi_araddr", 
        "axi_arlen", "axi_arsize", "axi_arburst", "axi_arlock",
        "axi_arcache", "axi_arprot", "axi_arqos", "axi_arregion", "axi_aruser"
    ],
    # Read Data Channel
    "AXI Read Data": [
        "axi_rvalid", "axi_rready", "axi_rid", "axi_rdata", 
        "axi_rresp", "axi_rlast", "axi_ruser"
    ],
    # Control Signals
    "Control": ["axi_aclk", "axi_aresetn"],
    # Internal State
    "Internal State": ["r_write_state", "r_read_state"]
}
```

## Debug Check Functions

### check_axi_write_addr_data_ordering

Checks if write address and data ordering follows protocol.

```python
async def check_axi_write_addr_data_ordering(dut, wave_gen)
```

- Detects when write data is sent before the associated address (protocol violation)

### check_axi_read_interleaving

Checks if read data is interleaved properly with IDs.

```python
async def check_axi_read_interleaving(dut, wave_gen)
```

- Detects when read responses are interleaved with different IDs
- Useful for verifying multi-master AXI implementations

### check_axi_write_resp_ordering

Checks write response ordering follows protocol.

```python
async def check_axi_write_resp_ordering(dut, wave_gen)
```

- Ensures write response is sent only after the last data transfer
- Detects protocol violations in response ordering

### check_axi_exclusive_access

Checks exclusive access protocol compliance.

```python
async def check_axi_exclusive_access(dut, wave_gen)
```

- Verifies proper exclusive access sequence
- Tracks exclusive read addresses

### check_axi_burst_boundary

Checks if AXI bursts cross 4KB boundaries (violation).

```python
async def check_axi_burst_boundary(dut, wave_gen)
```

- Detects burst transfers that cross 4KB address boundaries
- Calculates burst end address based on length and size parameters

### check_axi_handshake_stalls

Checks for stalled handshakes on any AXI channel.

```python
async def check_axi_handshake_stalls(dut, wave_gen)
```

- Monitors each channel's valid/ready pair for extended stalls
- Reports stalls that exceed a threshold

## Predefined AXI4 Scenarios

### axi4_write_scenario

Scenario for verifying AXI4 write transaction flow.

```python
axi4_write_scenario = ScenarioConfig(
    name="AXI4 Write Transaction",
    description="Verify AXI4 write transaction flow",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Write address and write data handshakes
        SignalRelation(...),
        SignalRelation(...),
        # Last write data triggers write response
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': check_axi_write_addr_data_ordering,
            'description': "Check address/data ordering"
        },
        {
            'function': check_axi_write_resp_ordering,
            'description': "Check write response ordering"
        },
        {
            'function': check_axi_burst_boundary,
            'description': "Check burst boundary"
        }
    ]
)
```

### axi4_read_scenario

Scenario for verifying AXI4 read transaction flow.

```python
axi4_read_scenario = ScenarioConfig(
    name="AXI4 Read Transaction",
    description="Verify AXI4 read transaction flow",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Read address handshake
        SignalRelation(...),
        # Address acceptance triggers read data
        SignalRelation(...),
        # Read data handshake
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': check_axi_read_interleaving,
            'description': "Check read interleaving"
        },
        {
            'function': check_axi_burst_boundary,
            'description': "Check burst boundary"
        }
    ]
)
```

### axi4_handshake_scenario

Scenario for verifying AXI4 handshake timing behavior.

```python
axi4_handshake_scenario = ScenarioConfig(
    name="AXI4 Handshake Timing",
    description="Verify AXI4 handshake timing behavior",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # All valid-ready handshake pairs for all five channels
        SignalRelation(...),
        SignalRelation(...),
        SignalRelation(...),
        SignalRelation(...),
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': check_axi_handshake_stalls,
            'description': "Check handshake stalls"
        }
    ]
)
```

### axi4_exclusive_scenario

Scenario for verifying AXI4 exclusive access behavior.

```python
axi4_exclusive_scenario = ScenarioConfig(
    name="AXI4 Exclusive Access",
    description="Verify AXI4 exclusive access behavior",
    pre_cycles=2,
    post_cycles=2,
    relations=[
        # Exclusive read followed by exclusive write
        SignalRelation(...),
        # Exclusive write response indicates success/failure
        SignalRelation(...)
    ],
    debug_checks=[
        {
            'function': check_axi_exclusive_access,
            'description': "Check exclusive access protocol"
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

- Dynamically detects which AXI4 signals are available in the DUT
- Creates appropriate signal groups based on available signals
- Organizes signals by AXI4 channel
- Falls back to predefined groups if no signals are found

### create_axi4_scenarios

Creates AXI4 scenarios based on available signals in the DUT.

```python
def create_axi4_scenarios(dut, include_scenarios=None):
    """
    Create AXI4 scenarios based on available signals in the DUT
    
    Args:
        dut: Device under test
        include_scenarios: Optional list of scenario names to include
                          (None = all available)
    
    Returns:
        List of applicable scenarios
    """
```

- Checks which AXI4 channels are available in the DUT
- Creates appropriate scenarios based on available signals
- Optionally filters scenarios based on the include_scenarios parameter
- Supports selective creation of read, write, handshake, and exclusive scenarios

## Example Usage

### Basic AXI4 Waveform Generation

```python
from CocoTBFramework.tbclasses.wavedrom_user import axi4
from CocoTBFramework.components.wavedrom_utils import WaveformContainer

@cocotb.test()
async def test_axi4_interface(dut):
    # Get AXI4 signal groups for this DUT
    signal_groups = axi4.get_signal_groups(dut)
    
    # Create applicable AXI4 scenarios
    scenarios = axi4.create_axi4_scenarios(dut)
    
    # Create waveform container
    container = WaveformContainer(
        title="AXI4 Interface Verification",
        clock_signal="axi_aclk",
        signal_groups=signal_groups,
        scenarios=scenarios
    )
    
    # Run all scenarios
    await container.run_all_scenarios(dut)
    
    # Generate WaveDrom output
    container.generate_wavedrom("axi4_verification.json")
```

### Selective Scenario Verification

```python
# Create only read and handshake scenarios
scenarios = axi4.create_axi4_scenarios(
    dut, 
    include_scenarios=["read", "handshake"]
)
```

## AXI4 Protocol Background

The AMBA AXI4 (Advanced eXtensible Interface 4) is a high-performance, high-frequency bus protocol designed for high-bandwidth and low-latency communication. Key characteristics include:

1. **Separate Channels**: Five independent channels for efficient operation
   - Write Address Channel
   - Write Data Channel
   - Write Response Channel
   - Read Address Channel
   - Read Data Channel

2. **Channel Architecture**:
   - Each channel uses a VALID/READY handshake mechanism
   - Data transfer occurs when both VALID and READY are asserted
   - Channels operate independently, allowing for overlapped operations

3. **Burst Transfers**:
   - Support for multiple data transfers with a single address phase
   - Four burst types: FIXED, INCR, WRAP, and unspecified
   - Maximum burst length of 256 beats in AXI4

4. **Transaction IDs**:
   - Support for out-of-order transaction completion
   - ID tags allow for transaction tracking and reordering

5. **Exclusive Access**:
   - Support for atomic operations via exclusive access mechanism
   - Used for implementing synchronization primitives

6. **Quality of Service**:
   - QoS signaling for prioritization of transactions
   - Region identifiers for system partitioning

## Implementation Notes

- The module automatically adapts to signal naming in the DUT
- Debug checks handle missing signals gracefully
- Burst boundary checks use DATA_WIDTH property if available
- Multiple address/data width configurations are supported
- Exclusive access monitoring works with tagged ID values
- The implementation can detect interleaved transactions in multi-master scenarios

## Best Practices

1. **Channel Checking**: Monitor all five AXI channels for comprehensive verification
2. **Burst Configuration**: Verify that burst parameters comply with AXI4 specifications
3. **Exclusive Access**: Ensure proper exclusive access sequence for atomic operations
4. **4KB Boundaries**: Confirm that bursts never cross 4KB address boundaries
5. **Handshake Stalls**: Monitor for extended handshake stalls that may indicate performance issues
6. **Transaction Ordering**: Verify correct ordering of address and data phases

## See Also

- [AXI4 Components](../../components/axi4/index.md) - AXI4 protocol components for CocoTB
- [AXI4 Scoreboard](../../scoreboards/axi4_scoreboard.md) - AXI4 transaction verification scoreboard

## Navigation

[↑ WaveDrom User Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
