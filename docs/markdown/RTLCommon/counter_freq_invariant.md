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

# Frequency Invariant Counter Module

## Overview
The `counter_freq_invariant` module is an advanced timing counter that maintains consistent time-based counting regardless of the input clock frequency. It uses a configurable prescaler to divide the input clock and provides a frequency-independent output counter, making it ideal for applications requiring consistent timing across different clock domains or frequencies.

## Module Declaration
```systemverilog
module counter_freq_invariant #(
    parameter int COUNTER_WIDTH = 5,      // Width of the output counter
    parameter int PRESCALER_MAX = 65536   // Maximum value of the pre-scaler
) (
    input  logic                        clk,         // Input clock
    input  logic                        rst_n,       // Active low reset
    input  logic                        sync_reset_n,// Synchronous reset signal
    input  logic [3:0]                  freq_sel,    // Frequency selection (configurable)
    output logic [COUNTER_WIDTH-1:0]    counter,     // 5-bit output counter
    output logic                        tick         // Pulse every time counter increments
);
```

## Parameters

### COUNTER_WIDTH
- **Type**: `int`
- **Default**: `5`
- **Description**: Bit width of the main output counter
- **Range**: 1 to 32 (practical range)
- **Impact**: Determines maximum count value (2^COUNTER_WIDTH - 1)

### PRESCALER_MAX  
- **Type**: `int`
- **Default**: `65536` 
- **Description**: Maximum division factor for the prescaler
- **Range**: Must be ≥ largest division factor (10000)
- **Usage**: Determines internal prescaler counter width

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk` | 1 | `logic` | Input clock signal (any frequency) |
| `rst_n` | 1 | `logic` | Active-low asynchronous reset |
| `sync_reset_n` | 1 | `logic` | Synchronous reset control |
| `freq_sel` | 4 | `logic` | Frequency selection (0-15) |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `counter` | COUNTER_WIDTH | `logic` | Main counter output |
| `tick` | 1 | `logic` | Pulse when counter increments |

## Frequency Selection Table

The module provides 16 predefined frequency divisions based on a 1GHz reference:

| freq_sel | Division Factor | Target Frequency | Period | Use Case |
|----------|-----------------|------------------|---------|----------|
| 4'b0000 | 1 | 1000MHz (1GHz) | 1ns | High-speed processing |
| 4'b0001 | 10 | 100MHz | 10ns | Standard FPGA operations |
| 4'b0010 | 20 | 50MHz | 20ns | Memory interfaces |
| 4'b0011 | 25 | 40MHz | 25ns | Display controllers |
| 4'b0100 | 40 | 25MHz | 40ns | Audio sampling |
| 4'b0101 | 50 | 20MHz | 50ns | Serial communications |
| 4'b0110 | 80 | 12.5MHz | 80ns | Sensor interfaces |
| 4'b0111 | 100 | 10MHz | 100ns | ADC/DAC timing |
| 4'b1000 | 125 | 8MHz | 125ns | Microcontroller speeds |
| 4'b1001 | 200 | 5MHz | 200ns | Slow peripherals |
| 4'b1010 | 250 | 4MHz | 250ns | Power-optimized |
| 4'b1011 | 500 | 2MHz | 500ns | Ultra-low power |
| 4'b1100 | 1000 | 1MHz | 1μs | Timing references |
| 4'b1101 | 2000 | 500kHz | 2μs | Human interface |
| 4'b1110 | 5000 | 200kHz | 5μs | LED refresh rates |
| 4'b1111 | 10000 | 100kHz | 10μs | Very slow timing |

## Architecture Overview

### Block Diagram
```
Input Clock → [Freq Change Detect] → [Prescaler Counter] → [Main Counter] → Output
                      ↓                       ↓                    ↓
                [Clear Pulse Gen]        [Division Config]     [Tick Gen]
```

### Internal Signals
```systemverilog
// Configuration (combinational)
logic [15:0] w_division_factor;     // Current division factor

// Change detection (flopped)
logic [3:0] r_prev_freq_sel;        // Previous freq_sel value
logic       r_clear_pulse;          // Frequency change indicator

// Prescaler interface
logic w_prescaler_done;             // Prescaler terminal count
```

## Implementation Details

### Frequency Configuration Logic
```systemverilog
always_comb begin
    case (freq_sel)
        4'b0000: w_division_factor = 16'd1;      // 1000MHz
        4'b0001: w_division_factor = 16'd10;     // 100MHz  
        4'b0010: w_division_factor = 16'd20;     // 50MHz
        4'b0011: w_division_factor = 16'd25;     // 40MHz
        4'b0100: w_division_factor = 16'd40;     // 25MHz
        4'b0101: w_division_factor = 16'd50;     // 20MHz
        4'b0110: w_division_factor = 16'd80;     // 12.5MHz
        4'b0111: w_division_factor = 16'd100;    // 10MHz
        4'b1000: w_division_factor = 16'd125;    // 8MHz
        4'b1001: w_division_factor = 16'd200;    // 5MHz
        4'b1010: w_division_factor = 16'd250;    // 4MHz
        4'b1011: w_division_factor = 16'd500;    // 2MHz
        4'b1100: w_division_factor = 16'd1000;   // 1MHz
        4'b1101: w_division_factor = 16'd2000;   // 500kHz
        4'b1110: w_division_factor = 16'd5000;   // 200kHz
        4'b1111: w_division_factor = 16'd10000;  // 100kHz
        default: w_division_factor = 16'd1;      // Safe default
    endcase
end
```

### Change Detection Logic
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_prev_freq_sel <= 4'b0;
        r_clear_pulse <= 1'b0;
    end else begin
        r_prev_freq_sel <= freq_sel;
        
        // Generate clear pulse when freq_sel changes or sync reset
        r_clear_pulse <= (freq_sel != r_prev_freq_sel) || !sync_reset_n;
    end
end
```

### Prescaler Implementation
The prescaler uses the `counter_load_clear` module to implement configurable division:

```systemverilog
counter_load_clear #(
    .MAX(PRESCALER_MAX)
) prescaler_counter(
    .clk(clk),
    .rst_n(rst_n),
    .clear(r_clear_pulse),           // Clear on frequency change
    .increment(1'b1),                // Always increment
    .load(1'b1),                     // Always load new value
    .loadval(w_division_factor[$clog2(PRESCALER_MAX)-1:0] - 1'b1),
    .done(w_prescaler_done),
    .count()                         // Unused
);
```

### Main Counter and Tick Generation
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        counter <= 'b0;
        tick <= 'b0;
    end else begin
        // Generate tick when prescaler completes and counter at max
        if (w_prescaler_done && &counter)
            tick <= 'b1;
        else
            tick <= 'b0;
        
        // Update main counter
        if (r_clear_pulse)
            counter <= 'b0;
        else if (w_prescaler_done)
            counter <= counter + 1'b1;  // Natural rollover
    end
end
```

## Timing Analysis

### Prescaler Operation
- **Load Value**: `division_factor - 1`
- **Count Cycles**: `division_factor` clock cycles per prescaler tick
- **Frequency**: `f_input / division_factor`

### Main Counter Operation
- **Increment Rate**: Prescaler tick rate
- **Roll-over**: At `2^COUNTER_WIDTH`
- **Tick Generation**: One cycle when counter is all 1's and prescaler completes

### Overall Timing
- **Counter Period**: `division_factor × 2^COUNTER_WIDTH` input clock cycles
- **Tick Period**: `division_factor` input clock cycles
- **Frequency Independence**: Same tick rate regardless of input frequency

## Design Examples

### 1. 1MHz Tick Generator (Any Input Clock)
```systemverilog
counter_freq_invariant #(
    .COUNTER_WIDTH(8),      // 8-bit counter (0-255)
    .PRESCALER_MAX(65536)   // Support up to 65536 division
) tick_1mhz (
    .clk(clk_any_freq),     // Could be 100MHz, 200MHz, etc.
    .rst_n(rst_n),
    .sync_reset_n(1'b1),
    .freq_sel(4'b1100),     // Select 1MHz (1000 division)
    .counter(timer_count),
    .tick(tick_1mhz)
);
```

### 2. Configurable Baud Rate Generator
```systemverilog
logic [3:0] baud_sel;
logic baud_tick;

// Baud rate selection mapping
// 4'b0111 = 10MHz → 115200 baud (10MHz/87 ≈ 115200)
// 4'b1001 = 5MHz → 57600 baud (5MHz/87 ≈ 57600)
// 4'b1100 = 1MHz → 9600 baud (1MHz/104 ≈ 9600)

counter_freq_invariant #(
    .COUNTER_WIDTH(4),
    .PRESCALER_MAX(10000)
) baud_gen (
    .clk(sys_clk),
    .rst_n(rst_n),
    .sync_reset_n(1'b1),
    .freq_sel(baud_sel),
    .counter(),             // Unused
    .tick(baud_tick)
);
```

### 3. Multi-Rate Timer System
```systemverilog
// Different timers for different purposes
counter_freq_invariant #(.COUNTER_WIDTH(6)) fast_timer (
    .freq_sel(4'b0001),     // 100MHz rate
    .tick(fast_tick),       // Every 10ns
    ...
);

counter_freq_invariant #(.COUNTER_WIDTH(8)) med_timer (
    .freq_sel(4'b0111),     // 10MHz rate  
    .tick(med_tick),        // Every 100ns
    ...
);

counter_freq_invariant #(.COUNTER_WIDTH(10)) slow_timer (
    .freq_sel(4'b1100),     // 1MHz rate
    .tick(slow_tick),       // Every 1μs
    ...
);
```

## Advanced Features

### Dynamic Frequency Switching
```systemverilog
// Example: Switch between fast and slow modes
logic power_save_mode;
logic [3:0] dynamic_freq_sel;

always_comb begin
    if (power_save_mode)
        dynamic_freq_sel = 4'b1111;  // 100kHz for power save
    else
        dynamic_freq_sel = 4'b0001;  // 100MHz for performance
end

counter_freq_invariant adaptive_timer (
    .freq_sel(dynamic_freq_sel),
    .sync_reset_n(!power_save_mode), // Reset when switching modes
    ...
);
```

### Synchronous Reset Applications
```systemverilog
// Reset timer when entering specific system state
logic enter_calibration_mode;

counter_freq_invariant cal_timer (
    .sync_reset_n(!enter_calibration_mode),
    .freq_sel(4'b1010),     // 4MHz for calibration
    ...
);
```

## Verification Strategy

### Test Scenarios
1. **Frequency Selection**: Test all 16 freq_sel values
2. **Dynamic Switching**: Change freq_sel during operation
3. **Reset Behavior**: Test both async and sync reset
4. **Tick Generation**: Verify tick timing at various frequencies
5. **Counter Rollover**: Test main counter wrap-around
6. **Prescaler Boundary**: Test prescaler terminal count

### Testbench Example
```systemverilog
module tb_counter_freq_invariant;
    logic clk, rst_n, sync_reset_n;
    logic [3:0] freq_sel;
    logic [4:0] counter;
    logic tick;
    
    // Clock generation - 100MHz
    initial clk = 0;
    always #5ns clk = ~clk;
    
    // Test sequence
    initial begin
        rst_n = 0;
        sync_reset_n = 1;
        freq_sel = 4'b0000;
        
        #100ns rst_n = 1;
        
        // Test different frequencies
        #1000ns freq_sel = 4'b0001; // 100MHz → 10MHz
        #1000ns freq_sel = 4'b0111; // 10MHz
        #1000ns freq_sel = 4'b1100; // 1MHz
        
        // Test synchronous reset
        #1000ns sync_reset_n = 0;
        #50ns sync_reset_n = 1;
        
        #10000ns $finish;
    end
    
    // Monitor tick frequency
    real tick_period, last_tick_time;
    always @(posedge tick) begin
        tick_period = $realtime - last_tick_time;
        last_tick_time = $realtime;
        $display("Tick period: %.2f ns (freq_sel=%b)", tick_period, freq_sel);
    end
endmodule
```

### Coverage Points
```systemverilog
covergroup freq_invariant_cg @(posedge clk);
    cp_freq_sel: coverpoint freq_sel {
        bins all_freqs[] = {[0:15]};
    }
    
    cp_counter: coverpoint counter {
        bins low = {[0:7]};
        bins mid = {[8:23]};
        bins high = {[24:31]};
    }
    
    cp_freq_change: coverpoint (freq_sel != $past(freq_sel)) {
        bins change = {1};
        bins stable = {0};
    }
    
    cp_sync_reset: coverpoint sync_reset_n {
        bins active = {0};
        bins inactive = {1};
    }
endgroup
```

## Performance Characteristics

### Resource Utilization
- **Prescaler Counter**: `$clog2(PRESCALER_MAX)` bits
- **Main Counter**: `COUNTER_WIDTH` bits  
- **Logic**: Division factor lookup table + change detection
- **Total FFs**: ~20-25 flip-flops for typical configuration

### Timing Performance
- **Maximum Frequency**: Limited by prescaler counter increment
- **Typical**: 200-400 MHz in modern FPGAs
- **Critical Path**: Prescaler increment + done detection

### Power Consumption
- **Dynamic**: Proportional to clock frequency and toggle rate
- **Optimization**: Higher division factors reduce overall power
- **Clock Gating**: Consider gating prescaler when not needed

## Applications

### Communication Systems
```systemverilog
// UART baud rate generation
counter_freq_invariant uart_baud (
    .freq_sel(baud_rate_sel),  // From configuration register
    .tick(baud_x16_tick),      // 16x oversampling
    ...
);
```

### Display Controllers
```systemverilog
// Pixel clock generation for different video modes
counter_freq_invariant pixel_clk (
    .freq_sel(video_mode_sel), // Different pixel rates
    .tick(pixel_enable),
    ...
);
```

### ADC/DAC Timing
```systemverilog
// Sample rate control independent of system clock
counter_freq_invariant sample_rate (
    .freq_sel(sample_rate_sel), // Audio sample rates
    .tick(conversion_trigger),
    ...
);
```

### Power Management
```systemverilog
// Frequency scaling for power optimization
counter_freq_invariant power_timer (
    .freq_sel(power_mode_sel),  // Fast/medium/slow/sleep
    .tick(power_event),
    ...
);
```

## Design Guidelines

### Parameter Selection
1. **COUNTER_WIDTH**: Choose based on maximum count needed
2. **PRESCALER_MAX**: Must be ≥ largest division factor (10000)
3. **freq_sel Mapping**: Customize division table for your application

### Reset Strategy
1. **Asynchronous Reset**: For system-wide reset
2. **Synchronous Reset**: For mode changes and state machine control
3. **Clear Pulse**: Automatically generated on frequency changes

### Frequency Planning
1. **Input Clock**: Can be any stable frequency
2. **Division Factors**: Choose based on target frequencies
3. **Jitter**: Higher division factors may accumulate jitter

## Troubleshooting

### Common Issues
1. **Incorrect Tick Rate**: Verify division factor calculation
2. **Missing Ticks**: Check for proper reset sequencing  
3. **Frequency Switching Glitches**: Ensure clean freq_sel transitions
4. **Timing Violations**: Pipeline if prescaler counter is too wide

### Debug Techniques
1. **Simulation**: Use time-based measurements to verify tick rates
2. **Logic Analyzer**: Capture actual tick timing in hardware
3. **Frequency Counter**: Measure actual output frequency
4. **Reset Analysis**: Check reset propagation and synchronization

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
