<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# dataint_checksum

## Overview

The `dataint_checksum` module is a simple accumulating checksum calculator. It keeps adding incoming data values into a running checksum you can use for basic data integrity verification. Nothing fancy — that's the point.

### Module Declaration

```systemverilog
module dataint_checksum #(
    parameter int WIDTH = 8
) (
    input  logic             clk,
    rst_n,
    input  logic             reset,
    input  logic             valid,
    input  logic [WIDTH-1:0] data,
    output logic [WIDTH-1:0] chksum
);
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `WIDTH` | 8 | Width of the data and checksum in bits |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | Input | 1 | Clock signal |
| `rst_n` | Input | 1 | Active-low asynchronous reset |
| `reset` | Input | 1 | Synchronous reset signal |
| `valid` | Input | 1 | Data valid signal - when high, data is accumulated |
| `data` | Input | WIDTH | Input data to be added to checksum |
| `chksum` | Output | WIDTH | Current checksum value |

## Functional Description

### Operation

The module keeps an internal counter (`r_count`) that accumulates incoming data:
- On reset (either asynchronous `rst_n` or synchronous `reset`), the counter clears to zero
- When `valid` is asserted, the input `data` is added to the current counter value
- The checksum output is simply the current counter value

### Reset Behavior

Two reset mechanisms, and you should know which one wins:
1. **Asynchronous Reset**: `rst_n` (active-low) immediately clears the counter
2. **Synchronous Reset**: `reset` (active-high) clears the counter on the next clock edge

### Key Features

- **Simple Accumulation**: Uses basic addition for checksum calculation
- **Parameterizable Width**: Supports any data width through the `WIDTH` parameter
- **Dual Reset Support**: Both asynchronous and synchronous reset capabilities
- **Enable Control**: Data accumulation only occurs when `valid` is asserted

### Special Considerations

- **Overflow Handling**: The checksum wraps around when the accumulated value exceeds the maximum representable in `WIDTH` bits — expected behavior for a checksum, not a bug
- **Continuous Output**: The checksum output is always valid and reflects the current accumulated value
- **Reset Priority**: Asynchronous reset (`rst_n`) takes precedence over synchronous reset (`reset`)

### State Machine

No formal FSM here — it operates as a simple accumulator with two states:
- **RESET**: Counter is zero
- **ACCUMULATING**: Counter adds valid data inputs

## Timing Characteristics

This module is **purely combinational** -- it contains no `always_ff` and no
latch, so it holds no state and adds no clock cycles. Its outputs settle a
propagation delay after its inputs, and it introduces no latency into a
pipeline that instantiates it.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples
```systemverilog
// 16-bit checksum calculator
dataint_checksum #(
    .WIDTH(16)
) checksum_calc (
    .clk(clk),
    .rst_n(rst_n),
    .reset(soft_reset),
    .valid(data_valid),
    .data(input_data),
    .chksum(calculated_checksum)
);
```

## Design Notes

### Common Applications

- Simple data integrity checking
- Packet checksum calculation
- Basic error detection in data streams
- Accumulation of data values for verification purposes

## Testing

`val/common/test_dataint_checksum.py` exercises this module. It collects 4 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/common/test_dataint_checksum.py -v
```

---

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
