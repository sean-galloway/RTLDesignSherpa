# Common Groups

## Overview

The `CommonGroups` class provides predefined signal groupings for standard hardware protocols, making it easier to organize signals in waveform diagrams. These groupings improve the readability of waveforms and provide a standardized way to display protocol-specific signals.

## Features

- Predefined signal groups for common protocols (AXI, APB, SPI, I2C, etc.)
- Easily combinable groups for complex interfaces
- Custom group creation functionality
- Consistent naming conventions across protocols

## Classes

### CommonGroups

A static class containing predefined signal groups for standard protocols.

#### Constants

- `CONTROL`: Basic control signals (clk, rst_n, en)
- `AXI_WRITE`: AXI write channel signals
- `AXI_READ`: AXI read channel signals
- `AXI_LITE`: AXI-Lite protocol signals
- `APB`: APB protocol signals
- `HANDSHAKE`: Basic handshake protocol signals (valid, ready)
- `REQ_ACK`: Request-acknowledge protocol signals (req, ack)
- `MEMORY`: Common memory interface signals
- `STATE_MACHINE`: Common state machine signals
- `SPI`: SPI protocol signals
- `I2C`: I2C protocol signals
- `UART`: UART protocol signals

#### Static Methods

```python
@staticmethod
def combine(*groups)
```
- Combines multiple signal groups into a single dictionary
- Args: `*groups` - Group dictionaries to combine
- Returns: Combined dictionary of all groups

```python
@staticmethod
def custom(name, signals)
```
- Creates a custom signal group
- Args:
  - `name`: Group name
  - `signals`: List of signal names
- Returns: Dictionary with custom group

## Example Usage

### Basic Group Selection

```python
from CocoTBFramework.components.wavedrom_utils import CommonGroups

# Use a predefined signal group
axi_write_signals = CommonGroups.AXI_WRITE

# Use in WaveDrom container
container = WaveformContainer(
    title="AXI Write Operation",
    clock_signal="clk",
    signal_groups=axi_write_signals,
    scenarios=[write_scenario]
)
```

### Combining Multiple Groups

```python
# Combine multiple protocol groups
combined_signals = CommonGroups.combine(
    CommonGroups.CONTROL,
    CommonGroups.APB,
    CommonGroups.STATE_MACHINE
)

# Use combined groups in waveform container
container = WaveformContainer(
    title="APB Controller",
    clock_signal="clk",
    signal_groups=combined_signals,
    scenarios=[apb_scenario]
)
```

### Creating Custom Groups

```python
# Create a custom signal group
custom_group = CommonGroups.custom(
    "DMA Control", 
    ["dma_start", "dma_done", "dma_error", "dma_addr", "dma_len"]
)

# Combine with standard groups
all_groups = CommonGroups.combine(
    CommonGroups.CONTROL,
    custom_group
)

# Use in WaveDrom container
container = WaveformContainer(
    title="DMA Controller",
    clock_signal="clk",
    signal_groups=all_groups,
    scenarios=[dma_scenario]
)
```

## AXI Protocol Signal Groups

The AXI protocol groups include the standard AMBA AXI signals:

### AXI Write

```python
AXI_WRITE = {
    "AXI Write": ["awvalid", "awready", "awaddr", "awlen", "awsize",
                  "wvalid", "wready", "wdata", "wstrb", "wlast",
                  "bvalid", "bready", "bresp"]
}
```

### AXI Read

```python
AXI_READ = {
    "AXI Read": ["arvalid", "arready", "araddr", "arlen", "arsize",
                "rvalid", "rready", "rdata", "rresp", "rlast"]
}
```

## APB Protocol Signal Group

The APB protocol group includes the standard AMBA APB signals:

```python
APB = {
    "APB": ["psel", "penable", "paddr", "pwrite", "pwdata", "prdata", "pready", "pslverr"]
}
```

## Simple Protocol Signal Groups

Several simpler protocols are also provided:

### Handshake Protocol

```python
HANDSHAKE = {
    "Handshake": ["valid", "ready"]
}
```

### Request-Acknowledge Protocol

```python
REQ_ACK = {
    "Request-Acknowledge": ["req", "ack"]
}
```

## Best Practices

1. **Consistent Naming**: Use lowercase signal names as shown in the predefined groups
2. **Group by Functionality**: Organize signals based on their functional relationships
3. **Combine Related Groups**: Use the `combine()` method to create comprehensive group sets
4. **Match RTL Names**: Custom groups should match the actual signal names in your RTL
5. **Hierarchical Organization**: For complex designs, create groups that reflect the design hierarchy

## See Also

- [Container](container.md) - Uses signal groups for waveform organization
- [Generator](generator.md) - Renders signal groups in WaveDrom format
- [Example Test](example_test.md) - Examples of using signal groups

## Navigation

[↑ WaveDrom Utils Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
