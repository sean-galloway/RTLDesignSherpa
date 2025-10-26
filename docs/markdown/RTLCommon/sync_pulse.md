# Pulse Synchronizer for Clock Domain Crossing

A safe pulse synchronizer that transfers single-cycle pulses between asynchronous clock domains using a toggle-based handshake with metastability filtering.

## Overview

The `sync_pulse` module provides metastability-safe pulse synchronization across clock domains. It converts a single-cycle pulse in the source clock domain into a single-cycle pulse in the destination clock domain, handling arbitrary clock frequency ratios. The module uses a toggle-register approach with multi-stage synchronization to guarantee no pulse loss when minimum spacing requirements are met.

## Module Declaration

```systemverilog
module sync_pulse #(
    parameter int SYNC_STAGES = 3    // Synchronizer depth (range: 2-4)
) (
    // Source clock domain
    input  logic i_src_clk,      // Source clock
    input  logic i_src_rst_n,    // Source reset (active-low)
    input  logic i_pulse,        // Input pulse (single-cycle high)

    // Destination clock domain
    input  logic i_dst_clk,      // Destination clock
    input  logic i_dst_rst_n,    // Destination reset (active-low)
    output logic o_pulse         // Output pulse (single-cycle high)
);
```

## Parameters

### User-Settable Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SYNC_STAGES | int | 3 | Number of synchronizer stages for metastability filtering (range: 2-4) |

**SYNC_STAGES Guidelines:**
- **2 stages**: Minimum CDC-safe, basic reliability
- **3 stages**: Recommended for most applications (>10^12 hours MTBF)
- **4 stages**: Ultra-high reliability (aerospace, medical)

## Ports

### Source Clock Domain Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_src_clk | Input | 1 | Source clock (where input pulse originates) |
| i_src_rst_n | Input | 1 | Source domain active-low asynchronous reset |
| i_pulse | Input | 1 | Input pulse (must be single-cycle high) |

### Destination Clock Domain Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_dst_clk | Input | 1 | Destination clock (where output pulse appears) |
| i_dst_rst_n | Input | 1 | Destination domain active-low asynchronous reset |
| o_pulse | Output | 1 | Synchronized output pulse (single-cycle high) |

## Functionality

### Toggle-Based Pulse Synchronization

The module uses a four-stage process to safely transfer pulses:

1. **Source Toggle**: Input pulse toggles `r_src_toggle` register
2. **Synchronization**: Toggle synchronized across clock domains via multi-stage synchronizer
3. **Edge Detection**: XOR detects toggle transitions to generate destination pulse
4. **Single-Cycle Output**: Output pulse is exactly one destination clock cycle wide

### Timing Characteristics

- **Latency**: `(SYNC_STAGES + 2)` destination clock cycles
- **Minimum Pulse Spacing**: `3 × T_dst + 2 × T_src` clock periods
- **MTBF**: >10^12 hours @ SYNC_STAGES=3, 100MHz

Where:
- `T_dst` = Destination clock period
- `T_src` = Source clock period

## Implementation Details

### Source Domain: Toggle Register

```systemverilog
(* ASYNC_REG = "TRUE" *) logic r_src_toggle;

always_ff @(posedge i_src_clk or negedge i_src_rst_n) begin
    if (!i_src_rst_n) begin
        r_src_toggle <= 1'b0;
    end else if (i_pulse) begin
        r_src_toggle <= ~r_src_toggle;  // Toggle on each pulse
    end
end
```

**Key Points:**
- Toggle persists across clock domains (quasi-static)
- Each pulse inverts toggle state (0→1 or 1→0)
- Toggle visible to destination synchronizer for multiple cycles

### Destination Domain: Multi-Stage Synchronizer

```systemverilog
(* ASYNC_REG = "TRUE" *) logic [SYNC_STAGES-1:0] r_sync;

always_ff @(posedge i_dst_clk or negedge i_dst_rst_n) begin
    if (!i_dst_rst_n) begin
        r_sync <= '0;
    end else begin
        r_sync <= {r_sync[SYNC_STAGES-2:0], r_src_toggle};  // Shift register
    end
end
```

**Metastability Filtering:**
- Stage 0: Captures source toggle (may go metastable)
- Stages 1 to N-1: Filter metastability exponentially
- Stage N-1: Clean synchronized toggle output

### Destination Domain: Edge Detection

```systemverilog
logic r_sync_prev;

// Delay synchronized toggle by one cycle
always_ff @(posedge i_dst_clk or negedge i_dst_rst_n) begin
    if (!i_dst_rst_n) begin
        r_sync_prev <= 1'b0;
    end else begin
        r_sync_prev <= r_sync[SYNC_STAGES-1];
    end
end

// XOR detects toggle edge (both rising and falling)
assign o_pulse = r_sync[SYNC_STAGES-1] ^ r_sync_prev;
```

**Edge Detection Logic:**
- Compares current toggle with previous toggle
- XOR: `0→1` or `1→0` transition generates pulse
- Output: Single-cycle high pulse in destination domain

## Protocol Timing

### Single Pulse Transfer

```
Source Clock:  __|‾|__|__|__|__|__|__|__|__|__|__|__
i_pulse:       __|‾|__|__|__|__|__|__|__|__|__|__|__
r_src_toggle:  ____|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

Dest Clock:    ___|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|_
r_sync[0]:     ______|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
r_sync[1]:     _________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
r_sync[2]:     ____________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
r_sync_prev:   _______________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
o_pulse:       ____________|‾|__|__|__|__|__|__|__|__

Latency: 5 destination clocks (SYNC_STAGES=3 + 2)
```

### Multiple Pulse Transfer

```
Source:   __|‾|__|__|‾|__|__|__|__|‾|__|__|__|__|__
          Pulse1    Pulse2          Pulse3

Dest:     ___|‾|__|__|__|‾|__|__|__|__|__|‾|__|__|_
          Out1           Out2              Out3

Note: Minimum 3 destination clock spacing maintained
```

## Usage Examples

### Basic Pulse Synchronization

```systemverilog
// Synchronize button press from slow to fast clock
sync_pulse #(
    .SYNC_STAGES(3)
) u_button_sync (
    .i_src_clk   (button_clk),        // Slow clock (debounced button)
    .i_src_rst_n (sys_rst_n),
    .i_pulse     (button_press),      // Single-cycle pulse
    .i_dst_clk   (core_clk),          // Fast core clock
    .i_dst_rst_n (sys_rst_n),
    .o_pulse     (button_press_sync)
);
```

### Interrupt Synchronization

```systemverilog
// Synchronize peripheral interrupt to CPU clock
sync_pulse #(
    .SYNC_STAGES(3)
) u_irq_sync (
    .i_src_clk   (periph_clk),
    .i_src_rst_n (periph_rst_n),
    .i_pulse     (periph_irq_pulse),  // Interrupt pulse
    .i_dst_clk   (cpu_clk),
    .i_dst_rst_n (cpu_rst_n),
    .o_pulse     (cpu_irq)
);

// Use synchronized interrupt in CPU
always_ff @(posedge cpu_clk) begin
    if (cpu_irq) begin
        // Handle interrupt
        irq_pending <= 1'b1;
    end
end
```

### Event Counter Synchronization

```systemverilog
// Count events across clock domains
logic [15:0] event_count;

sync_pulse #(
    .SYNC_STAGES(3)
) u_event_sync (
    .i_src_clk   (sensor_clk),
    .i_src_rst_n (sys_rst_n),
    .i_pulse     (sensor_event),
    .i_dst_clk   (sys_clk),
    .i_dst_rst_n (sys_rst_n),
    .o_pulse     (event_sync)
);

// Count synchronized events
always_ff @(posedge sys_clk or negedge sys_rst_n) begin
    if (!sys_rst_n) begin
        event_count <= 16'h0;
    end else if (event_sync) begin
        event_count <= event_count + 16'h1;
    end
end
```

### With Edge Detector for Multi-Cycle Signals

```systemverilog
// Convert multi-cycle signal to single-cycle pulse first
logic multi_cycle_sig, single_cycle_pulse;

edge_detect u_edge_det (
    .clk      (src_clk),
    .rst_n    (src_rst_n),
    .sig_in   (multi_cycle_sig),
    .pulse_out(single_cycle_pulse)   // Rising edge → pulse
);

// Then synchronize the pulse
sync_pulse #(
    .SYNC_STAGES(3)
) u_sync (
    .i_src_clk   (src_clk),
    .i_src_rst_n (src_rst_n),
    .i_pulse     (single_cycle_pulse),
    .i_dst_clk   (dst_clk),
    .i_dst_rst_n (dst_rst_n),
    .o_pulse     (pulse_sync)
);
```

## Design Considerations

### When to Use sync_pulse

✅ **Appropriate Use Cases:**
- Single-cycle pulse events (interrupts, triggers, strobes)
- Event counters across clock domains
- Handshake acknowledgments
- Sporadic control signals (button presses, sensor events)
- Timeout/watchdog pulses

❌ **Inappropriate Use Cases:**
- High-frequency continuous pulses (use async FIFO)
- Data buses (use handshake or FIFO)
- Multi-bit values (use `glitch_free_n_dff_arn` with Gray code)
- Clocks themselves (use dedicated clock crossing primitives)

### Minimum Pulse Spacing

To avoid pulse loss, ensure minimum spacing between source pulses:

**Fast Source → Slow Destination:**
```
Min spacing = 3 × T_dst + 2 × T_src

Example: 100MHz src → 25MHz dst
T_src = 10ns, T_dst = 40ns
Min spacing = 3×40ns + 2×10ns = 140ns = 14 source clocks
```

**Slow Source → Fast Destination:**
```
Min spacing = 3 × T_dst + 2 × T_src

Example: 10MHz src → 100MHz dst
T_src = 100ns, T_dst = 10ns
Min spacing = 3×10ns + 2×100ns = 230ns = 2.3 source clocks
(Round up: 3 source clocks minimum)
```

### Reset Synchronization

Both resets should be properly synchronized to their respective clock domains:

```systemverilog
// Proper reset synchronization
reset_sync u_src_rst_sync (
    .clk        (i_src_clk),
    .async_rst_n(global_rst_n),
    .sync_rst_n (i_src_rst_n)
);

reset_sync u_dst_rst_sync (
    .clk        (i_dst_clk),
    .async_rst_n(global_rst_n),
    .sync_rst_n (i_dst_rst_n)
);
```

## Synthesis and Constraints

### Synthesis Attributes

The module includes ASYNC_REG attributes to prevent optimization:

```systemverilog
(* ASYNC_REG = "TRUE" *) logic r_src_toggle;
(* ASYNC_REG = "TRUE" *) logic [SYNC_STAGES-1:0] r_sync;
```

These attributes:
- Prevent register duplication
- Ensure synchronizer stages stay together
- Help tools recognize CDC paths

### Timing Constraints (Xilinx XDC)

```tcl
# Mark clock domain crossing paths as false paths
set_false_path -from [get_clocks i_src_clk] -to [get_pins -hierarchical *r_sync_reg[0]/D]

# Or set maximum delay for CDC analysis
set_max_delay -from [get_clocks i_src_clk] -to [get_pins -hierarchical *r_sync_reg[0]/D] -datapath_only [get_property PERIOD [get_clocks i_dst_clk]]

# Set ASYNC_REG property (if not in RTL)
set_property ASYNC_REG TRUE [get_cells -hierarchical *r_sync_reg*]
```

### Timing Constraints (Intel SDC)

```tcl
# Set false path for CDC
set_false_path -from [get_clocks i_src_clk] -to [get_registers *r_sync[0]]

# Mark synchronizer chain
set_instance_assignment -name SYNCHRONIZER_IDENTIFICATION "FORCED IF ASYNCHRONOUS" -to *r_sync*
```

## Verification and Assertions

### Formal Assertions (Built-in)

The module includes formal assertions for verification:

```systemverilog
// Assert: Input pulse is single-cycle
property p_single_cycle_pulse;
    @(posedge i_src_clk) disable iff (!i_src_rst_n)
    i_pulse |=> !i_pulse;
endproperty

// Assert: Output pulse is single-cycle
property p_output_single_cycle;
    @(posedge i_dst_clk) disable iff (!i_dst_rst_n)
    o_pulse |=> !o_pulse;
endproperty
```

### Simulation Checks

```systemverilog
// Check input pulse width
always @(posedge i_src_clk) begin
    if (i_pulse) begin
        @(posedge i_src_clk);
        assert (!i_pulse) else $error("Input pulse must be single-cycle");
    end
end

// Check minimum pulse spacing
int last_pulse_time = 0;
always @(posedge i_dst_clk) begin
    if (o_pulse) begin
        int time_diff = $time - last_pulse_time;
        assert (time_diff >= 3*T_dst)
            else $warning("Pulse spacing too close: %0d ns", time_diff);
        last_pulse_time = $time;
    end
end
```

## Performance Analysis

### Latency Breakdown

For SYNC_STAGES=3:
1. Source toggle register: 1 source clock
2. Synchronizer stages: 3 destination clocks
3. Edge detection: 1 destination clock
4. Output pulse generation: 1 destination clock

**Total**: 5 destination clocks + 1 source clock

### Resource Utilization

| Component | FFs | LUTs | Description |
|-----------|-----|------|-------------|
| r_src_toggle | 1 | 1 | Source toggle register |
| r_sync | SYNC_STAGES | 0 | Synchronizer chain |
| r_sync_prev | 1 | 0 | Previous toggle storage |
| o_pulse | 0 | 1 | XOR edge detector |
| **Total** | **SYNC_STAGES+2** | **2** | Minimal footprint |

## Common Pitfalls

❌ **Anti-Pattern 1**: Multi-cycle input pulses
```systemverilog
// WRONG: Input pulse held for multiple cycles
i_pulse <= 1'b1;
#(2*CLK_PERIOD);
i_pulse <= 1'b0;

// Result: May generate multiple output pulses

// RIGHT: Single-cycle pulse
i_pulse <= 1'b1;
#CLK_PERIOD;
i_pulse <= 1'b0;
```

❌ **Anti-Pattern 2**: Pulses too close together
```systemverilog
// WRONG: Back-to-back pulses in source domain
forever begin
    i_pulse <= 1'b1;
    #CLK_PERIOD;
    i_pulse <= 1'b0;
    #CLK_PERIOD;  // Only 1 clock gap!
end

// Result: Pulse loss

// RIGHT: Adequate spacing
forever begin
    i_pulse <= 1'b1;
    #CLK_PERIOD;
    i_pulse <= 1'b0;
    #(MIN_SPACING*CLK_PERIOD);  // Meet minimum spacing
end
```

❌ **Anti-Pattern 3**: Using for data transfer
```systemverilog
// WRONG: Trying to transfer data with pulse
logic [7:0] data_to_sync;
always @(posedge src_clk) begin
    if (send_data) begin
        data_to_sync <= new_data;  // Will be corrupted!
        i_pulse <= 1'b1;
    end
end

// RIGHT: Use handshake or async FIFO for data
```

## Related Modules

- **glitch_free_n_dff_arn.sv** - Multi-bit signal synchronization (quasi-static)
- **reset_sync.sv** - Specialized reset synchronization
- **edge_detect.sv** - Edge-to-pulse conversion (single clock domain)
- **async_fifo.sv** - For high-throughput data CDC
- **handshake_sync.sv** - Multi-bit data CDC with handshake

## References

- Cummings, Clifford E. "Clock Domain Crossing (CDC) Design & Verification Techniques Using SystemVerilog." SNUG 2008.
- "Synthesis and Scripting Techniques for Designing Multi-Asynchronous Clock Designs." Xilinx WP275.
- IEEE 1800-2017 SystemVerilog LRM - Clock Domain Crossing

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
