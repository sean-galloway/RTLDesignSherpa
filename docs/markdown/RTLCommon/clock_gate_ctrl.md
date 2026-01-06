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

# Clock Gate Controller - Comprehensive Documentation

## Overview
The `clock_gate_ctrl` module implements an intelligent clock gating controller that automatically stops the clock when a circuit block becomes idle, significantly reducing dynamic power consumption. It features configurable idle timeout, immediate wake-up capability, and safe clock gating using integrated clock gate (ICG) cells.

## Module Declaration
```systemverilog
module clock_gate_ctrl #(
    parameter int IDLE_CNTR_WIDTH = 4,
    parameter int N = IDLE_CNTR_WIDTH
) (
    // Inputs
    input logic          clk_in,
    input logic          aresetn,
    input logic          cfg_cg_enable,     // Global clock gate enable
    input logic  [N-1:0] cfg_cg_idle_count, // Idle countdown value
    input logic          wakeup,            // Signal to wake up the block

    // Outputs
    output logic         clk_out,
    output logic         gating            // clock gating indicator
);
```

## Parameters

### IDLE_CNTR_WIDTH
- **Type**: `int`
- **Default**: `4`
- **Description**: Bit width of the idle timeout counter
- **Range**: 2 to 16 bits (practical range)
- **Impact**: Determines maximum idle timeout (2^IDLE_CNTR_WIDTH - 1 cycles)
- **Power Trade-off**: Larger counters allow longer timeouts but consume more power

### N
- **Type**: `int`
- **Default**: `IDLE_CNTR_WIDTH`
- **Description**: Alias for counter width (convenience parameter)
- **Usage**: Internal consistency check and code readability

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk_in` | 1 | `logic` | Input clock to be gated |
| `aresetn` | 1 | `logic` | Active-low asynchronous reset |
| `cfg_cg_enable` | 1 | `logic` | Global clock gating enable control |
| `cfg_cg_idle_count` | N | `logic` | Idle timeout value (configuration) |
| `wakeup` | 1 | `logic` | Immediate wake-up signal |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk_out` | 1 | `logic` | Gated output clock |
| `gating` | 1 | `logic` | Clock gating status indicator |

## Clock Gating Theory

### Why Clock Gating?
Clock gating is one of the most effective power reduction techniques:
- **Dynamic Power**: P = C × V² × f × α (α = switching activity)
- **Clock Networks**: Typically consume 20-40% of total chip power
- **Gating Benefits**: Can reduce power by 50-90% in idle blocks
- **Area Overhead**: Minimal (< 5% for typical designs)

### Clock Gating Safety
Proper clock gating requires:
1. **Glitch-Free**: No spurious clock edges during gating transitions
2. **Setup/Hold**: Adequate timing margins around gating decisions
3. **Reset Handling**: Proper behavior during reset conditions
4. **Tool Support**: Use of qualified ICG (Integrated Clock Gate) cells

## Architecture and Implementation

### Idle Counter Logic
```systemverilog
logic [N-1:0] r_idle_counter;

always_ff @(posedge clk_in or negedge aresetn) begin
    if (!aresetn) begin
        r_idle_counter <= cfg_cg_idle_count;
    end else begin
        if (wakeup || !cfg_cg_enable) begin
            // On wakeup or global disable, reset counter
            r_idle_counter <= cfg_cg_idle_count;
        end else if (r_idle_counter != 'h0) begin
            // Normal counting operation - decrement when not zero
            r_idle_counter <= r_idle_counter - 1'b1;
        end
        // When counter reaches zero, it stays at zero
    end
end
```

### Gating Control Logic
```systemverilog
wire w_gate_enable = cfg_cg_enable && !wakeup && (r_idle_counter == 'h0);

// Instantiate the ICG cell
icg u_icg (
    .clk(clk_in),
    .en(~w_gate_enable),  // Enable is active high in ICG
    .gclk(clk_out)
);

assign gating = w_gate_enable;
```

### State Machine Behavior
The controller operates as a countdown timer with three states:

1. **ACTIVE State**: Counter loaded with `cfg_cg_idle_count`
2. **COUNTDOWN State**: Counter decrements each cycle when no activity
3. **GATED State**: Counter at zero, clock is gated off

### Timing Diagram
```
clk_in:          __|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__
wakeup:          _______|‾‾‾|__________________________|‾‾‾|___
cfg_cg_enable:   |‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|
r_idle_counter:  <3><2><3><2><1><0><0><0><0><0><0><0><0><3><2>
gating:          __________________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|____
clk_out:         __|‾|__|‾|__|‾|__|‾|__|___________________|‾|__|‾
```

## ICG (Integrated Clock Gate) Cell

### Standard ICG Interface
```systemverilog
module icg (
    input  logic clk,    // Input clock
    input  logic en,     // Enable (active high)
    output logic gclk    // Gated clock output
);
    
    // Implementation varies by technology library
    // Typically includes:
    // - Latch to avoid glitches
    // - AND gate for gating
    // - Proper setup/hold timing
    
endmodule
```

### ICG Implementation (Conceptual)
```systemverilog
// Simplified ICG implementation (technology-specific)
module icg_generic (
    input  logic clk,
    input  logic en,
    output logic gclk
);

    logic en_latched;
    
    // Latch enable on falling edge to avoid glitches
    always_latch begin
        if (~clk)
            en_latched = en;
    end
    
    // Gate clock with latched enable
    assign gclk = clk & en_latched;

endmodule
```

## Design Examples and Applications

### 1. CPU Core Clock Gating
```systemverilog
module cpu_clock_gating (
    input  logic        clk_cpu,
    input  logic        rst_n,
    
    // CPU control signals
    input  logic        cpu_active,
    input  logic        interrupt_pending,
    input  logic        debug_mode,
    
    // Power management
    input  logic [3:0]  idle_threshold,
    input  logic        power_save_enable,
    
    // Output clocks
    output logic        clk_cpu_gated,
    output logic        clk_debug,
    output logic        cpu_sleeping
);

    logic cpu_wakeup;
    logic debug_wakeup;
    
    // CPU wake-up conditions
    assign cpu_wakeup = cpu_active || interrupt_pending;
    
    // Debug interface always active in debug mode
    assign debug_wakeup = debug_mode || cpu_wakeup;
    
    // Main CPU clock gating
    clock_gate_ctrl #(
        .IDLE_CNTR_WIDTH(4)
    ) cpu_gate (
        .clk_in(clk_cpu),
        .aresetn(rst_n),
        .cfg_cg_enable(power_save_enable),
        .cfg_cg_idle_count(idle_threshold),
        .wakeup(cpu_wakeup),
        .clk_out(clk_cpu_gated),
        .gating(cpu_sleeping)
    );
    
    // Debug clock gating (shorter timeout)
    clock_gate_ctrl #(
        .IDLE_CNTR_WIDTH(3)
    ) debug_gate (
        .clk_in(clk_cpu),
        .aresetn(rst_n),
        .cfg_cg_enable(power_save_enable && !debug_mode),
        .cfg_cg_idle_count(3'd2), // Short timeout for debug
        .wakeup(debug_wakeup),
        .clk_out(clk_debug),
        .gating() // Unused
    );

endmodule
```

### 2. Peripheral Interface Clock Management
```systemverilog
module peripheral_clock_manager (
    input  logic        clk_system,
    input  logic        rst_n,
    
    // Peripheral activity signals
    input  logic        uart_active,
    input  logic        spi_active,
    input  logic        i2c_active,
    input  logic        timer_active,
    
    // Configuration
    input  logic [7:0]  power_config,   // [7:4] = enable bits, [3:0] = timeout
    
    // Gated clocks
    output logic        clk_uart,
    output logic        clk_spi,
    output logic        clk_i2c,
    output logic        clk_timer,
    
    // Status
    output logic [3:0]  peripheral_sleeping
);

    logic [3:0] idle_timeout;
    logic [3:0] gate_enables;
    
    assign idle_timeout = power_config[3:0];
    assign gate_enables = power_config[7:4];
    
    // UART clock gating
    clock_gate_ctrl #(4) uart_cg (
        .clk_in(clk_system),
        .aresetn(rst_n),
        .cfg_cg_enable(gate_enables[0]),
        .cfg_cg_idle_count(idle_timeout),
        .wakeup(uart_active),
        .clk_out(clk_uart),
        .gating(peripheral_sleeping[0])
    );
    
    // SPI clock gating
    clock_gate_ctrl #(4) spi_cg (
        .clk_in(clk_system),
        .aresetn(rst_n),
        .cfg_cg_enable(gate_enables[1]),
        .cfg_cg_idle_count(idle_timeout),
        .wakeup(spi_active),
        .clk_out(clk_spi),
        .gating(peripheral_sleeping[1])
    );
    
    // I2C clock gating
    clock_gate_ctrl #(4) i2c_cg (
        .clk_in(clk_system),
        .aresetn(rst_n),
        .cfg_cg_enable(gate_enables[2]),
        .cfg_cg_idle_count(idle_timeout),
        .wakeup(i2c_active),
        .clk_out(clk_i2c),
        .gating(peripheral_sleeping[2])
    );
    
    // Timer clock gating (different timeout)
    clock_gate_ctrl #(4) timer_cg (
        .clk_in(clk_system),
        .aresetn(rst_n),
        .cfg_cg_enable(gate_enables[3]),
        .cfg_cg_idle_count(4'd1), // Quick timeout for timers
        .wakeup(timer_active),
        .clk_out(clk_timer),
        .gating(peripheral_sleeping[3])
    );

endmodule
```

### 3. Memory Subsystem Clock Gating
```systemverilog
module memory_clock_gating (
    input  logic        clk_memory,
    input  logic        rst_n,
    
    // Memory access signals
    input  logic        mem_read,
    input  logic        mem_write,
    input  logic        mem_refresh_req,
    input  logic        cache_miss,
    
    // Configuration
    input  logic [2:0]  mem_power_mode,  // 0=always on, 7=aggressive gating
    
    // Gated clocks
    output logic        clk_mem_ctrl,    // Memory controller
    output logic        clk_mem_data,    // Data path
    output logic        clk_mem_refresh, // Refresh logic
    
    // Status
    output logic [2:0]  mem_gating_status
);

    logic [3:0] timeout_ctrl, timeout_data, timeout_refresh;
    logic mem_active, data_active, refresh_active;
    
    // Activity detection
    assign mem_active = mem_read || mem_write || cache_miss;
    assign data_active = mem_read || mem_write;
    assign refresh_active = mem_refresh_req;
    
    // Timeout configuration based on power mode
    always_comb begin
        case (mem_power_mode)
            3'd0: {timeout_ctrl, timeout_data, timeout_refresh} = {4'd15, 4'd15, 4'd15}; // Always on
            3'd1: {timeout_ctrl, timeout_data, timeout_refresh} = {4'd10, 4'd8, 4'd12};  // Conservative
            3'd2: {timeout_ctrl, timeout_data, timeout_refresh} = {4'd8, 4'd6, 4'd10};   // Moderate
            3'd3: {timeout_ctrl, timeout_data, timeout_refresh} = {4'd6, 4'd4, 4'd8};    // Balanced
            3'd4: {timeout_ctrl, timeout_data, timeout_refresh} = {4'd4, 4'd2, 4'd6};    // Aggressive
            3'd5: {timeout_ctrl, timeout_data, timeout_refresh} = {4'd2, 4'd1, 4'd4};    // Very aggressive
            3'd6: {timeout_ctrl, timeout_data, timeout_refresh} = {4'd1, 4'd0, 4'd2};    // Maximum power save
            3'd7: {timeout_ctrl, timeout_data, timeout_refresh} = {4'd0, 4'd0, 4'd1};    // Ultra power save
        endcase
    end
    
    // Memory controller clock gating
    clock_gate_ctrl #(4) ctrl_cg (
        .clk_in(clk_memory),
        .aresetn(rst_n),
        .cfg_cg_enable(mem_power_mode != 0),
        .cfg_cg_idle_count(timeout_ctrl),
        .wakeup(mem_active),
        .clk_out(clk_mem_ctrl),
        .gating(mem_gating_status[0])
    );
    
    // Data path clock gating
    clock_gate_ctrl #(4) data_cg (
        .clk_in(clk_memory),
        .aresetn(rst_n),
        .cfg_cg_enable(mem_power_mode != 0),
        .cfg_cg_idle_count(timeout_data),
        .wakeup(data_active),
        .clk_out(clk_mem_data),
        .gating(mem_gating_status[1])
    );
    
    // Refresh logic clock gating
    clock_gate_ctrl #(4) refresh_cg (
        .clk_in(clk_memory),
        .aresetn(rst_n),
        .cfg_cg_enable(mem_power_mode > 2), // Only gate in aggressive modes
        .cfg_cg_idle_count(timeout_refresh),
        .wakeup(refresh_active),
        .clk_out(clk_mem_refresh),
        .gating(mem_gating_status[2])
    );

endmodule
```

### 4. Adaptive Clock Gating with Activity Monitoring
```systemverilog
module adaptive_clock_gating #(
    parameter int ACTIVITY_WINDOW = 256  // Activity monitoring window
) (
    input  logic        clk_in,
    input  logic        rst_n,
    
    // Activity signals
    input  logic [7:0]  activity_vector,
    
    // Configuration
    input  logic        adaptive_enable,
    input  logic [3:0]  base_timeout,
    
    // Outputs
    output logic        clk_out,
    output logic        gating_active,
    output logic [7:0]  activity_level    // Activity percentage
);

    logic [15:0] activity_counter;
    logic [7:0] activity_window_counter;
    logic [3:0] adaptive_timeout;
    logic block_active;
    
    // Activity monitoring
    always_ff @(posedge clk_in or negedge rst_n) begin
        if (!rst_n) begin
            activity_counter <= 0;
            activity_window_counter <= 0;
            activity_level <= 0;
        end else begin
            // Count activity in current window
            if (|activity_vector)
                activity_counter <= activity_counter + 1;
                
            activity_window_counter <= activity_window_counter + 1;
            
            // Update activity level at end of window
            if (activity_window_counter == ACTIVITY_WINDOW - 1) begin
                activity_level <= activity_counter[15:8]; // Scale to 0-255
                activity_counter <= 0;
                activity_window_counter <= 0;
            end
        end
    end
    
    // Adaptive timeout based on activity level
    always_comb begin
        if (!adaptive_enable) begin
            adaptive_timeout = base_timeout;
        end else begin
            case (activity_level)
                8'h00: adaptive_timeout = base_timeout + 4'd8; // Very low activity
                8'h01: adaptive_timeout = base_timeout + 4'd6; // Low activity  
                8'h02: adaptive_timeout = base_timeout + 4'd4; // Medium-low activity
                8'h04: adaptive_timeout = base_timeout + 4'd2; // Medium activity
                8'h08: adaptive_timeout = base_timeout;        // Normal activity
                default: adaptive_timeout = (base_timeout > 2) ? base_timeout - 2 : 0; // High activity
            endcase
        end
    end
    
    // Activity detection
    assign block_active = |activity_vector;
    
    // Clock gating controller
    clock_gate_ctrl #(4) adaptive_cg (
        .clk_in(clk_in),
        .aresetn(rst_n),
        .cfg_cg_enable(1'b1),
        .cfg_cg_idle_count(adaptive_timeout),
        .wakeup(block_active),
        .clk_out(clk_out),
        .gating(gating_active)
    );

endmodule
```

### 5. Hierarchical Clock Gating System
```systemverilog
module hierarchical_clock_gating (
    input  logic        clk_root,
    input  logic        rst_n,
    
    // Global control
    input  logic        global_cg_enable,
    input  logic [3:0]  global_timeout,
    
    // Subsystem activity
    input  logic        cpu_active,
    input  logic        dsp_active,
    input  logic        peripheral_active,
    input  logic        memory_active,
    
    // Hierarchical clocks
    output logic        clk_cpu_domain,
    output logic        clk_dsp_domain,
    output logic        clk_peripheral_domain,
    output logic        clk_memory_domain,
    
    // Power monitoring
    output logic [3:0]  domain_gating_status,
    output logic [15:0] power_savings_estimate
);

    logic system_active;
    logic clk_system_gated;
    logic system_gated;
    
    // System-level activity detection
    assign system_active = cpu_active || dsp_active || peripheral_active || memory_active;
    
    // Top-level system clock gating
    clock_gate_ctrl #(4) system_cg (
        .clk_in(clk_root),
        .aresetn(rst_n),
        .cfg_cg_enable(global_cg_enable),
        .cfg_cg_idle_count(global_timeout + 4'd4), // Longer timeout for system level
        .wakeup(system_active),
        .clk_out(clk_system_gated),
        .gating(system_gated)
    );
    
    // CPU domain gating
    clock_gate_ctrl #(4) cpu_cg (
        .clk_in(clk_system_gated),
        .aresetn(rst_n),
        .cfg_cg_enable(global_cg_enable && !system_gated),
        .cfg_cg_idle_count(global_timeout),
        .wakeup(cpu_active),
        .clk_out(clk_cpu_domain),
        .gating(domain_gating_status[0])
    );
    
    // DSP domain gating
    clock_gate_ctrl #(4) dsp_cg (
        .clk_in(clk_system_gated),
        .aresetn(rst_n),
        .cfg_cg_enable(global_cg_enable && !system_gated),
        .cfg_cg_idle_count(global_timeout - 1), // Aggressive for DSP
        .wakeup(dsp_active),
        .clk_out(clk_dsp_domain),
        .gating(domain_gating_status[1])
    );
    
    // Peripheral domain gating
    clock_gate_ctrl #(4) peripheral_cg (
        .clk_in(clk_system_gated),
        .aresetn(rst_n),
        .cfg_cg_enable(global_cg_enable && !system_gated),
        .cfg_cg_idle_count(global_timeout + 1), // Conservative for peripherals
        .wakeup(peripheral_active),
        .clk_out(clk_peripheral_domain),
        .gating(domain_gating_status[2])
    );
    
    // Memory domain gating
    clock_gate_ctrl #(4) memory_cg (
        .clk_in(clk_system_gated),
        .aresetn(rst_n),
        .cfg_cg_enable(global_cg_enable && !system_gated),
        .cfg_cg_idle_count(global_timeout + 2), // Conservative for memory
        .wakeup(memory_active),
        .clk_out(clk_memory_domain),
        .gating(domain_gating_status[3])
    );
    
    // Power savings estimation (simplified)
    logic [3:0] gated_domains;
    assign gated_domains = domain_gating_status[3:0];
    
    always_ff @(posedge clk_root or negedge rst_n) begin
        if (!rst_n) begin
            power_savings_estimate <= 0;
        end else begin
            // Rough power savings estimate (percentage)
            case ({system_gated, gated_domains})
                5'b1_0000: power_savings_estimate <= 16'd9000; // 90% savings
                5'b0_1111: power_savings_estimate <= 16'd7000; // 70% savings
                5'b0_1110: power_savings_estimate <= 16'd6000; // 60% savings
                5'b0_1100: power_savings_estimate <= 16'd5000; // 50% savings
                5'b0_1000: power_savings_estimate <= 16'd3000; // 30% savings
                5'b0_0100: power_savings_estimate <= 16'd2000; // 20% savings
                5'b0_0010: power_savings_estimate <= 16'd1500; // 15% savings
                5'b0_0001: power_savings_estimate <= 16'd1000; // 10% savings
                default:   power_savings_estimate <= 16'd0000; // 0% savings
            endcase
        end
    end

endmodule
```

## Advanced Features

### 1. Glitch-Free Clock Switching
```systemverilog
module glitch_free_clock_gate (
    input  logic clk_in,
    input  logic rst_n,
    input  logic gate_enable,
    input  logic wakeup,
    output logic clk_out
);

    logic gate_enable_sync;
    logic gate_request;
    
    // Synchronize gate enable to avoid glitches
    always_ff @(posedge clk_in or negedge rst_n) begin
        if (!rst_n) begin
            gate_enable_sync <= 0;
            gate_request <= 0;
        end else begin
            gate_enable_sync <= gate_enable;
            gate_request <= gate_enable_sync && !wakeup;
        end
    end
    
    // Use ICG with synchronized control
    icg u_icg (
        .clk(clk_in),
        .en(~gate_request),
        .gclk(clk_out)
    );

endmodule
```

### 2. Multi-Level Clock Gating
```systemverilog
module multi_level_clock_gate #(
    parameter int LEVELS = 3
) (
    input  logic             clk_in,
    input  logic             rst_n,
    input  logic [LEVELS-1:0] level_enables,
    input  logic [LEVELS-1:0] level_wakeups,
    input  logic [4*LEVELS-1:0] level_timeouts,
    output logic             clk_out,
    output logic [LEVELS-1:0] level_gating_status
);

    logic [LEVELS:0] clk_levels; // Include input clock
    assign clk_levels[0] = clk_in;
    
    genvar i;
    generate
        for (i = 0; i < LEVELS; i++) begin : level_gates
            logic [3:0] timeout;
            assign timeout = level_timeouts[i*4+:4];
            
            clock_gate_ctrl #(4) level_cg (
                .clk_in(clk_levels[i]),
                .aresetn(rst_n),
                .cfg_cg_enable(level_enables[i]),
                .cfg_cg_idle_count(timeout),
                .wakeup(|level_wakeups[LEVELS-1:i]), // Wake if any higher level active
                .clk_out(clk_levels[i+1]),
                .gating(level_gating_status[i])
            );
        end
    endgenerate
    
    assign clk_out = clk_levels[LEVELS];

endmodule
```

## Verification and Testing

### Comprehensive Test Bench
```systemverilog
module tb_clock_gate_ctrl;

    parameter IDLE_CNTR_WIDTH = 4;
    
    logic clk_in, aresetn;
    logic cfg_cg_enable;
    logic [IDLE_CNTR_WIDTH-1:0] cfg_cg_idle_count;
    logic wakeup;
    logic clk_out, gating;
    
    // Clock generation
    initial clk_in = 0;
    always #5ns clk_in = ~clk_in; // 100MHz
    
    // DUT instantiation
    clock_gate_ctrl #(
        .IDLE_CNTR_WIDTH(IDLE_CNTR_WIDTH)
    ) dut (.*);
    
    // Test sequence
    initial begin
        // Initialize
        aresetn = 0;
        cfg_cg_enable = 0;
        cfg_cg_idle_count = 4'd5;
        wakeup = 0;
        
        #100ns aresetn = 1;
        
        // Test basic gating
        test_basic_gating();
        
        // Test immediate wakeup
        test_immediate_wakeup();
        
        // Test global disable
        test_global_disable();
        
        // Test different timeouts
        test_timeout_values();
        
        $display("All tests completed!");
        $finish;
    end
    
    // Test basic clock gating functionality
    task test_basic_gating();
        begin
            $display("Testing basic clock gating...");
            
            cfg_cg_enable = 1;
            cfg_cg_idle_count = 4'd3;
            
            // Wait for gating to occur
            wait_for_gating();
            
            // Verify clock is gated
            check_clock_gated();
            
            // Wake up and verify clock restoration
            wakeup = 1;
            #20ns wakeup = 0;
            check_clock_active();
        end
    endtask
    
    // Wait for clock gating to occur
    task wait_for_gating();
        int timeout_cycles;
        begin
            timeout_cycles = 0;
            while (!gating && timeout_cycles < 100) begin
                @(posedge clk_in);
                timeout_cycles++;
            end
            
            if (!gating) begin
                $error("Clock gating did not occur within timeout");
            end else begin
                $display("Clock gating occurred after %d cycles", timeout_cycles);
            end
        end
    endtask
    
    // Check that clock is properly gated
    task check_clock_gated();
        logic prev_clk_out;
        int stable_cycles;
        begin
            prev_clk_out = clk_out;
            stable_cycles = 0;
            
            repeat (10) begin
                @(posedge clk_in);
                if (clk_out == prev_clk_out) begin
                    stable_cycles++;
                end else begin
                    stable_cycles = 0;
                    prev_clk_out = clk_out;
                end
            end
            
            if (stable_cycles >= 5) begin
                $display("PASS: Clock is properly gated");
            end else begin
                $error("FAIL: Clock is not properly gated");
            end
        end
    endtask
    
    // Check that clock is active
    task check_clock_active();
        int edge_count;
        begin
            edge_count = 0;
            
            repeat (20) begin
                @(posedge clk_in);
                if ($rose(clk_out)) edge_count++;
            end
            
            if (edge_count >= 8) begin
                $display("PASS: Clock is active after wakeup");
            end else begin
                $error("FAIL: Clock not properly restored after wakeup");
            end
        end
    endtask

endmodule
```

### Coverage Model
```systemverilog
covergroup clock_gate_cg @(posedge clk_in);
    
    cp_idle_count: coverpoint cfg_cg_idle_count {
        bins short_timeout[] = {[0:3]};
        bins medium_timeout[] = {[4:10]};
        bins long_timeout[] = {[11:15]};
    }
    
    cp_counter_values: coverpoint dut.r_idle_counter {
        bins countdown[] = {[0:15]};
        bins zero = {0};
    }
    
    cp_gating_enable: coverpoint cfg_cg_enable {
        bins enabled = {1};
        bins disabled = {0};
    }
    
    cp_wakeup: coverpoint wakeup {
        bins active = {1};
        bins inactive = {0};
    }
    
    cp_gating_status: coverpoint gating {
        bins gated = {1};
        bins ungated = {0};
    }
    
    // Cross coverage
    cross_timeout_gating: cross cp_idle_count, cp_gating_status;
    cross_wakeup_gating: cross cp_wakeup, cp_gating_status;

endcovergroup
```

### Formal Verification Properties
```systemverilog
module clock_gate_properties;

    // Bind to DUT
    bind clock_gate_ctrl clock_gate_properties props_inst (.*);
    
    // Property: Immediate wakeup
    property immediate_wakeup;
        @(posedge clk_in) disable iff (!aresetn)
        wakeup |-> ##1 !gating;
    endproperty
    
    // Property: Gating after timeout
    property gating_after_timeout;
        @(posedge clk_in) disable iff (!aresetn)
        cfg_cg_enable && !wakeup && (dut.r_idle_counter == 0) |-> gating;
    endproperty
    
    // Property: Counter behavior
    property counter_countdown;
        @(posedge clk_in) disable iff (!aresetn)
        cfg_cg_enable && !wakeup && (dut.r_idle_counter > 0) |=>
        (dut.r_idle_counter == $past(dut.r_idle_counter) - 1);
    endproperty
    
    // Property: Global disable
    property global_disable;
        @(posedge clk_in) disable iff (!aresetn)
        !cfg_cg_enable |-> !gating;
    endproperty
    
    // Assertions
    assert property (immediate_wakeup);
    assert property (gating_after_timeout);
    assert property (counter_countdown);
    assert property (global_disable);

endmodule
```

## Power Analysis and Optimization

### Power Savings Calculation
```systemverilog
module power_analysis_wrapper (
    input  logic        clk_in,
    input  logic        rst_n,
    input  logic        cfg_cg_enable,
    input  logic [3:0]  cfg_cg_idle_count,
    input  logic        wakeup,
    output logic        clk_out,
    output logic        gating,
    output logic [15:0] power_savings_percent
);

    // Clock gate controller
    clock_gate_ctrl #(4) cg_ctrl (
        .clk_in(clk_in),
        .aresetn(rst_n),
        .cfg_cg_enable(cfg_cg_enable),
        .cfg_cg_idle_count(cfg_cg_idle_count),
        .wakeup(wakeup),
        .clk_out(clk_out),
        .gating(gating)
    );
    
    // Power monitoring
    logic [31:0] total_cycles;
    logic [31:0] gated_cycles;
    logic [31:0] ungated_cycles;
    
    always_ff @(posedge clk_in or negedge rst_n) begin
        if (!rst_n) begin
            total_cycles <= 0;
            gated_cycles <= 0;
            ungated_cycles <= 0;
        end else begin
            total_cycles <= total_cycles + 1;
            if (gating)
                gated_cycles <= gated_cycles + 1;
            else
                ungated_cycles <= ungated_cycles + 1;
        end
    end
    
    // Calculate power savings percentage
    always_ff @(posedge clk_in) begin
        if (total_cycles > 1000) begin // Avoid division by small numbers
            power_savings_percent <= (gated_cycles * 100) / total_cycles;
        end else begin
            power_savings_percent <= 0;
        end
    end

endmodule
```

### Technology-Specific ICG Implementation
```systemverilog
// Example for TSMC technology
module icg_tsmc (
    input  logic clk,
    input  logic en,
    output logic gclk
);

    // Technology-specific implementation
    CKGTPBUF_X1M_A9TH u_icg (
        .CK(clk),
        .E(en),
        .GCK(gclk)
    );

endmodule

// Example for Intel/Altera technology
module icg_intel (
    input  logic clk,
    input  logic en,
    output logic gclk
);

    // Intel FPGA implementation
    logic en_reg;
    
    always_ff @(negedge clk) begin
        en_reg <= en;
    end
    
    assign gclk = clk & en_reg;

endmodule

// Generic behavioral model
module icg_behavioral (
    input  logic clk,
    input  logic en,
    output logic gclk
);

    logic en_latch;
    
    // Latch enable on falling edge to prevent glitches
    always_latch begin
        if (!clk)
            en_latch = en;
    end
    
    // Gate the clock
    assign gclk = clk & en_latch;

endmodule
```

## Synthesis Considerations

### Resource Utilization
| Configuration | LUTs | FFs | ICG Cells | Area Overhead |
|---------------|------|-----|-----------|---------------|
| 4-bit counter | 8 | 4 | 1 | < 2% |
| 8-bit counter | 15 | 8 | 1 | < 3% |
| 16-bit counter | 30 | 16 | 1 | < 5% |

### Timing Constraints
```tcl
# SDC constraints for clock gating
create_clock -name clk_in -period 10.0 [get_ports clk_in]

# Clock gating timing
set_case_analysis 0 [get_pins u_icg/en]
set_case_analysis 1 [get_pins u_icg/en]

# Setup/hold for gating control
set_input_delay -clock clk_in -max 2.0 [get_ports wakeup]
set_input_delay -clock clk_in -min 0.5 [get_ports wakeup]

# Clock gating cell timing
set_clock_gating_check -setup 0.2 -hold 0.1 [get_pins u_icg/en]
```

### Power Intent (UPF)
```tcl
# UPF power intent for clock gating
create_power_domain PD_MAIN
create_power_domain PD_GATED

# Clock gating specification
set_domain_supply_net PD_MAIN -primary_power_net VDD -primary_ground_net VSS
set_domain_supply_net PD_GATED -primary_power_net VDD -primary_ground_net VSS

# Clock gating control
create_power_switch PS_GATED \
    -domain PD_GATED \
    -input_supply_port {vin VDD} \
    -output_supply_port {vout VDD_GATED} \
    -control_port {ctrl gating} \
    -on_state {on vin {!ctrl}}
```

## Design Guidelines and Best Practices

### 1. Timeout Selection
```systemverilog
// Guidelines for timeout values
parameter TIMEOUT_GUIDELINES = {
    "CPU cores: 4-16 cycles",
    "Memory controllers: 8-32 cycles", 
    "Peripherals: 16-64 cycles",
    "Debug interfaces: 2-8 cycles",
    "Always-on domains: Disable gating"
};
```

### 2. Activity Signal Design
```systemverilog
// Good activity signal examples
logic cpu_active;
assign cpu_active = instruction_fetch || 
                   data_access || 
                   interrupt_processing ||
                   debug_access;

// Avoid overly broad activity signals
logic bad_activity;
assign bad_activity = |all_system_signals; // Too broad

// Avoid overly narrow activity signals  
logic narrow_activity;
assign narrow_activity = specific_register_write; // Too narrow
```

### 3. Hierarchical Gating Strategy
```
System Level (Longest timeout)
├── CPU Domain (Medium timeout)
│   ├── ALU (Short timeout)
│   ├── Cache (Medium timeout)
│   └── Debug (Very short timeout)
├── DSP Domain (Short timeout)
├── Peripheral Domain (Long timeout)
└── Memory Domain (Medium timeout)
```

### 4. Verification Checklist
- [ ] Verify gating occurs after correct timeout
- [ ] Verify immediate wakeup functionality
- [ ] Test global enable/disable
- [ ] Check reset behavior
- [ ] Validate power savings measurements
- [ ] Test all timeout configurations
- [ ] Verify clock integrity (no glitches)
- [ ] Check setup/hold timing margins

## Common Applications Summary

1. **CPU Power Management**: Core, cache, and pipeline clock gating
2. **Peripheral Controllers**: UART, SPI, I2C, timer clock gating
3. **Memory Subsystems**: Controller, data path, refresh logic gating
4. **Graphics/Video**: Pixel processing, display controller gating
5. **Communication Blocks**: Baseband, RF, protocol stack gating
6. **Test and Debug**: Scan chains, JTAG, debug interface gating
7. **AI/ML Accelerators**: Compute engine, memory interface gating

## Troubleshooting Guide

### Common Issues
1. **Clock Glitches**: Use qualified ICG cells, proper setup/hold margins
2. **Timing Violations**: Ensure adequate timing margins for gating signals
3. **Unexpected Gating**: Check activity signal connectivity and logic
4. **Power Not Saved**: Verify clock tree reaches gated logic
5. **Reset Issues**: Ensure proper reset sequencing and distribution

### Debug Techniques
1. **Simulation**: Monitor gating signals and clock activity
2. **Power Analysis**: Use tools to measure actual power savings
3. **Timing Analysis**: Check setup/hold violations on gating paths
4. **Logic Analyzer**: Capture real-time gating behavior in hardware
5. **Power Profiling**: Measure current consumption with/without gating

The clock gate controller provides an essential power management capability, enabling significant dynamic power reduction with minimal area overhead and design complexity. Proper implementation requires careful attention to timing, safety, and verification to ensure reliable operation while maximizing power savings.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
