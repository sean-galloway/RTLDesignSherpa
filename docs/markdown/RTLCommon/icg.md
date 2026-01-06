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

# icg

An Integrated Clock Gating (ICG) module that provides controlled clock gating for power optimization in digital designs.

## Overview

The `icg` module implements a latch-based clock gating cell that allows selective disabling of clock signals to reduce dynamic power consumption. This is a fundamental power management technique used extensively in modern ASIC and FPGA designs.

## Module Declaration

```systemverilog
module icg(
    input  logic en,
    input  logic clk,
    output logic gclk
);
```

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| en | 1 | Enable signal - when high, allows clock to pass through |
| clk | 1 | Input clock signal to be gated |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| gclk | 1 | Gated clock output - clk when en=1, low when en=0 |

## Functionality

### Clock Gating Operation

The ICG module implements a safe clock gating scheme that:

1. **Latches Enable Signal**: Uses a negative-edge triggered latch to capture the enable signal
2. **Prevents Glitches**: Ensures the enable signal is stable during clock high periods
3. **Generates Gated Clock**: ANDs the latched enable with the input clock

### Implementation Details

```systemverilog
logic en_out;

// Latch-based approach - enable is latched on clock low
always_latch begin
    if (!clk) begin
        en_out = en;
    end
end

// Generate gated clock
assign gclk = en_out && clk;
```

## Timing Characteristics

### Critical Timing Requirements

| Characteristic | Description |
|----------------|-------------|
| Setup Time | `en` must be stable before `clk` rising edge |
| Hold Time | `en` must remain stable after `clk` rising edge |
| Propagation Delay | Delay from `clk` to `gclk` through AND gate |
| Enable Latching | `en` is latched when `clk` is low |

### Timing Diagram

```
Clock Cycle:    |1    |2    |3    |4    |5    |
                |     |     |     |     |     |
clk      ____   |  ___   |  ___   |  ___   |  ___
            |___|     |___|     |___|     |___|
                |     |     |     |     |     |
en       ____   |     |     |___________     |
            |___|     |     |           |_____|
                |     |     |     |     |     |
en_out   ____   |     |_____|_____|_____|  ___
            |___|     |                 |_____|
                |     |     |     |     |     |
gclk     ____   |     | ___ | ___ | ___ |  ___
            |___|     ||___|||___|||___|||_____|
```

## Power Optimization Benefits

### Dynamic Power Reduction

The ICG module reduces dynamic power consumption by:

- **Clock Tree Power**: Eliminates switching activity in downstream clock networks
- **Register Power**: Prevents unnecessary flip-flop transitions when data is not changing
- **Combinational Power**: Reduces spurious switching in logic fed by gated registers

### Power Savings Calculation

Typical power savings achievable:
- **Clock Network**: 20-40% reduction in clock tree power
- **Sequential Logic**: 30-60% reduction in flip-flop power
- **Overall Dynamic Power**: 10-30% depending on gating efficiency

## Design Considerations

### Safety Requirements

- **Glitch-Free Operation**: Latch-based design prevents glitches on gated clock
- **Setup/Hold Timing**: Enable signal must meet timing requirements relative to clock
- **Clock Domain**: All logic using `gclk` must be in the same clock domain

### Enable Signal Guidelines

```systemverilog
// Good: Enable changes during clock low period
always_ff @(posedge clk) begin
    if (rst_n) begin
        enable_reg <= new_enable_value;  // Changes on clock edge
    end
end

// Caution: Ensure enable is stable during clock high
assign icg_enable = enable_reg && additional_condition;
```

## Usage Examples

### Basic Register Bank Gating

```systemverilog
// Clock gating for a register bank
logic bank_enable;
logic gated_clk;

icg u_bank_icg (
    .en   (bank_enable),
    .clk  (sys_clk),
    .gclk (gated_clk)
);

// Register bank using gated clock
always_ff @(posedge gated_clk or negedge rst_n) begin
    if (!rst_n) begin
        register_bank <= '0;
    end else begin
        register_bank <= next_register_values;
    end
end
```

### CPU Pipeline Stage Gating

```systemverilog
// Pipeline stage clock gating
logic pipe_stage_valid;
logic stage_clk;

icg u_pipe_icg (
    .en   (pipe_stage_valid),
    .clk  (cpu_clk),
    .gclk (stage_clk)
);

// Pipeline stage registers
always_ff @(posedge stage_clk or negedge rst_n) begin
    if (!rst_n) begin
        pipe_stage_regs <= '0;
    end else begin
        pipe_stage_regs <= pipe_stage_inputs;
    end
end
```

### Memory Interface Gating

```systemverilog
// Memory controller clock gating
logic mem_access_active;
logic mem_clk;

icg u_mem_icg (
    .en   (mem_access_active),
    .clk  (system_clk),
    .gclk (mem_clk)
);

assign mem_access_active = mem_read_req || mem_write_req || mem_busy;
```

## Implementation Alternatives

### Standard Cell ICG

Many ASIC libraries provide optimized ICG cells:

```systemverilog
// Using library ICG cell (example)
CLOCK_GATE_ICG u_lib_icg (
    .CLK    (clk),
    .EN     (en),
    .GCLK   (gclk)
);
```

### FPGA Implementation

For FPGA targets, use dedicated clock control primitives:

```systemverilog
// Xilinx BUFGCE example
BUFGCE u_bufgce (
    .I  (clk),
    .CE (en),
    .O  (gclk)
);
```

## Verification Considerations

### Functional Tests

- **Enable/Disable**: Verify correct gating behavior for enable transitions
- **Clock Integrity**: Ensure gated clock maintains proper duty cycle when enabled
- **Reset Behavior**: Verify proper operation during reset sequences

### Timing Tests

```systemverilog
// Timing verification example
initial begin
    // Test enable setup/hold timing
    @(negedge clk);
    en = 1'b1;  // Enable during clock low
    @(posedge clk);
    // Verify gclk follows clk

    @(negedge clk);
    en = 1'b0;  // Disable during clock low
    @(posedge clk);
    // Verify gclk remains low
end
```

### Power Analysis

- **Activity Monitoring**: Track switching activity reduction in gated domains
- **Power Estimation**: Measure power savings using EDA power analysis tools
- **Efficiency Metrics**: Calculate gating efficiency (% time clock is disabled)

## Synthesis Guidelines

### Technology Mapping

- **ASIC**: Use library-specific ICG cells for optimal area/power/timing
- **FPGA**: Map to dedicated clock control primitives (BUFGCE, etc.)
- **Timing Closure**: Account for additional setup/hold requirements

### Clock Tree Synthesis

```tcl
# Example synthesis constraints for ICG
set_case_analysis 0 [get_pins u_icg/en]  ;# For power analysis
set_clock_gating_check -setup 0.1 [get_pins u_icg/gclk]
set_clock_gating_check -hold 0.1 [get_pins u_icg/gclk]
```

## Design Integration

### Clock Tree Integration

The ICG should be placed strategically in the clock tree:

```
Main Clock → ICG → Local Clock Tree → Registers
           ↑
     Enable Logic
```

### Power Domain Considerations

- **Retention**: Ensure enable logic remains powered during clock gating
- **Isolation**: Properly isolate gated domains in multi-voltage designs
- **Power Sequencing**: Coordinate with power management units

## Related Modules

- `clock_gate_ctrl`: Enhanced clock gating controller with additional features
- `clock_divider`: Clock frequency division functionality
- `reset_sync`: Reset synchronization for gated clock domains

The `icg` module provides a fundamental building block for power-efficient digital design, enabling significant power savings through controlled clock gating while maintaining design safety and functionality.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
