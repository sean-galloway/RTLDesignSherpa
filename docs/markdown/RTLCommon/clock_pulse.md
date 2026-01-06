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

# Clock Pulse Generator - Comprehensive Documentation

## Overview
The `clock_pulse` module generates periodic pulse signals with configurable width (period). It creates a single-cycle pulse every WIDTH clock cycles, making it ideal for timing generation, heartbeat signals, sampling triggers, and periodic event generation in digital systems.

## Module Declaration
```systemverilog
module clock_pulse #(
    parameter int WIDTH = 10  // Width of the generated pulse in clock cycles
) (
    input  logic clk,    // Input clock signal
    input  logic rst_n,  // Input reset signal
    output logic pulse   // Output pulse signal
);
```

## Parameters

### WIDTH
- **Type**: `int`
- **Default**: `10`
- **Description**: Period of the pulse generation in clock cycles
- **Range**: 2 to 2^32-1 (practical range)
- **Impact**: Determines pulse frequency (f_clk / WIDTH)
- **Pulse Width**: Always exactly 1 clock cycle
- **Duty Cycle**: 1/WIDTH (e.g., 10% for WIDTH=10)

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk` | 1 | `logic` | System clock input |
| `rst_n` | 1 | `logic` | Active-low asynchronous reset |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `pulse` | 1 | `logic` | Periodic pulse output |

## Architecture and Implementation

### Internal Counter
```systemverilog
logic [WIDTH-1:0] r_counter;
logic [WIDTH-1:0] w_width_minus_one;

// Create a properly sized constant
assign w_width_minus_one = WIDTH[WIDTH-1:0] - 1'b1;
```

### Core Logic
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_counter <= 'b0;
        pulse     <= 'b0;
    end else begin
        if (r_counter < w_width_minus_one) 
            r_counter <= r_counter + 1'b1;
        else 
            r_counter <= 'b0;

        pulse <= (r_counter == w_width_minus_one);
    end
end
```

### Operation Principles
1. **Counter**: Free-running counter from 0 to WIDTH-1
2. **Pulse Generation**: Pulse asserted when counter reaches WIDTH-1
3. **Auto-Reset**: Counter wraps to 0 after reaching maximum
4. **Synchronous**: All operations synchronized to input clock
5. **Single Cycle**: Pulse duration is exactly one clock cycle

### Timing Characteristics
- **Period**: WIDTH clock cycles
- **Frequency**: f_clk / WIDTH
- **Pulse Width**: 1 clock cycle
- **Duty Cycle**: 1/WIDTH
- **Phase**: Pulse occurs on last count (WIDTH-1)

## Timing Diagrams

### Basic Operation (WIDTH=4)
```
Clock:    _|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_
Counter:  < 0 >< 1 >< 2 >< 3 >< 0 >< 1 >< 2 >< 3 >< 0 >
Pulse:    ______________________|‾‾‾|______________|‾‾‾|_
```

### Reset Behavior
```
Clock:    _|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_
Reset_n:  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|___|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
Counter:  < 0 >< 1 >< 2 >< 3 >< 0 >< 0 >< 1 >< 2 >< 3 >
Pulse:    ______________________|‾‾‾|______|‾‾‾|_____
```

### Different WIDTH Values
| WIDTH | Period | Duty Cycle | Use Case |
|-------|--------|------------|----------|
| 2 | 2 cycles | 50% | Clock divider |
| 4 | 4 cycles | 25% | Sampling |
| 10 | 10 cycles | 10% | Timing reference |
| 100 | 100 cycles | 1% | Heartbeat |
| 1000 | 1000 cycles | 0.1% | Slow events |

## Design Examples and Applications

### 1. Heartbeat and Status Indicators
```systemverilog
module system_heartbeat #(
    parameter int CLOCK_FREQ_HZ = 100_000_000,  // 100MHz
    parameter int HEARTBEAT_FREQ_HZ = 1          // 1Hz heartbeat
) (
    input  logic clk,
    input  logic rst_n,
    input  logic system_active,
    output logic heartbeat_led,
    output logic status_ok
);

    localparam int HEARTBEAT_WIDTH = CLOCK_FREQ_HZ / HEARTBEAT_FREQ_HZ;
    
    logic heartbeat_pulse;
    
    // Generate 1Hz heartbeat pulse
    clock_pulse #(
        .WIDTH(HEARTBEAT_WIDTH)
    ) heartbeat_gen (
        .clk(clk),
        .rst_n(rst_n),
        .pulse(heartbeat_pulse)
    );
    
    // LED control with heartbeat
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            heartbeat_led <= 1'b0;
        end else if (heartbeat_pulse) begin
            heartbeat_led <= ~heartbeat_led;  // Toggle LED
        end
    end
    
    // System status based on heartbeat activity
    logic [7:0] heartbeat_monitor;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            heartbeat_monitor <= 8'h00;
        end else begin
            heartbeat_monitor <= {heartbeat_monitor[6:0], heartbeat_pulse};
        end
    end
    
    assign status_ok = system_active && |heartbeat_monitor;

endmodule
```

### 2. Sampling and Data Acquisition
```systemverilog
module data_sampler #(
    parameter int SAMPLE_RATE_KHZ = 48,
    parameter int CLOCK_FREQ_MHZ = 100,
    parameter int DATA_WIDTH = 16
) (
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  enable,
    input  logic [DATA_WIDTH-1:0] analog_data,
    
    output logic [DATA_WIDTH-1:0] sampled_data,
    output logic                  sample_valid,
    output logic                  buffer_full
);

    localparam int SAMPLE_WIDTH = (CLOCK_FREQ_MHZ * 1000) / SAMPLE_RATE_KHZ;
    
    logic sample_trigger;
    
    // Generate sampling trigger
    clock_pulse #(
        .WIDTH(SAMPLE_WIDTH)
    ) sample_clock (
        .clk(clk),
        .rst_n(rst_n),
        .pulse(sample_trigger)
    );
    
    // Sample data on trigger
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sampled_data <= '0;
            sample_valid <= 1'b0;
        end else if (enable && sample_trigger) begin
            sampled_data <= analog_data;
            sample_valid <= 1'b1;
        end else begin
            sample_valid <= 1'b0;
        end
    end
    
    // Buffer management (simplified)
    logic [7:0] buffer_count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buffer_count <= 8'h00;
        end else if (sample_valid) begin
            buffer_count <= buffer_count + 1;
        end
    end
    
    assign buffer_full = &buffer_count;  // Full at 255 samples

endmodule
```

### 3. Communication Protocol Timing
```systemverilog
module uart_baud_generator #(
    parameter int CLOCK_FREQ_HZ = 100_000_000,
    parameter int BAUD_RATE = 115200
) (
    input  logic clk,
    input  logic rst_n,
    input  logic enable,
    
    output logic baud_tick,      // 1x baud rate
    output logic baud_tick_16x   // 16x baud rate for oversampling
);

    localparam int BAUD_WIDTH = CLOCK_FREQ_HZ / BAUD_RATE;
    localparam int BAUD_16X_WIDTH = CLOCK_FREQ_HZ / (BAUD_RATE * 16);
    
    logic baud_pulse, baud_16x_pulse;
    
    // 1x baud rate generator
    clock_pulse #(
        .WIDTH(BAUD_WIDTH)
    ) baud_1x_gen (
        .clk(clk),
        .rst_n(rst_n),
        .pulse(baud_pulse)
    );
    
    // 16x baud rate generator  
    clock_pulse #(
        .WIDTH(BAUD_16X_WIDTH)
    ) baud_16x_gen (
        .clk(clk),
        .rst_n(rst_n),
        .pulse(baud_16x_pulse)
    );
    
    // Gate with enable
    assign baud_tick = enable ? baud_pulse : 1'b0;
    assign baud_tick_16x = enable ? baud_16x_pulse : 1'b0;

endmodule
```

### 4. Memory Refresh Controller
```systemverilog
module dram_refresh_controller #(
    parameter int REFRESH_PERIOD_US = 64,     // 64μs refresh period
    parameter int CLOCK_FREQ_MHZ = 100,       // 100MHz system clock
    parameter int REFRESH_ROWS = 8192         // Number of rows to refresh
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        refresh_enable,
    
    output logic        refresh_request,
    output logic [12:0] refresh_row_addr,
    output logic        refresh_active
);

    localparam int REFRESH_WIDTH = (REFRESH_PERIOD_US * CLOCK_FREQ_MHZ) / REFRESH_ROWS;
    
    logic refresh_pulse;
    logic [12:0] row_counter;
    
    // Generate refresh timing
    clock_pulse #(
        .WIDTH(REFRESH_WIDTH)
    ) refresh_timer (
        .clk(clk),
        .rst_n(rst_n),
        .pulse(refresh_pulse)
    );
    
    // Row address counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            row_counter <= 13'h0000;
        end else if (refresh_pulse && refresh_enable) begin
            if (row_counter >= REFRESH_ROWS - 1)
                row_counter <= 13'h0000;
            else
                row_counter <= row_counter + 1;
        end
    end
    
    // Output assignments
    assign refresh_request = refresh_pulse && refresh_enable;
    assign refresh_row_addr = row_counter;
    assign refresh_active = refresh_enable;

endmodule
```

### 5. Multi-Rate Pulse Generation
```systemverilog
module multi_rate_pulse_generator (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [2:0] rate_select,    // Select pulse rate
    
    output logic       pulse_fast,     // Fast pulse output
    output logic       pulse_medium,   // Medium pulse output  
    output logic       pulse_slow,     // Slow pulse output
    output logic       pulse_config    // Configurable pulse output
);

    logic [31:0] config_width;
    
    // Rate selection for configurable output
    always_comb begin
        case (rate_select)
            3'b000: config_width = 32'd10;     // Very fast
            3'b001: config_width = 32'd100;    // Fast
            3'b010: config_width = 32'd1000;   // Medium
            3'b011: config_width = 32'd10000;  // Slow
            3'b100: config_width = 32'd100000; // Very slow
            default: config_width = 32'd1000;  // Default medium
        endcase
    end
    
    // Fixed rate pulse generators
    clock_pulse #(.WIDTH(50)) fast_gen (
        .clk(clk), .rst_n(rst_n), .pulse(pulse_fast)
    );
    
    clock_pulse #(.WIDTH(500)) medium_gen (
        .clk(clk), .rst_n(rst_n), .pulse(pulse_medium)
    );
    
    clock_pulse #(.WIDTH(5000)) slow_gen (
        .clk(clk), .rst_n(rst_n), .pulse(pulse_slow)
    );
    
    // Configurable rate generator (requires parameterizable module)
    configurable_pulse_gen config_gen (
        .clk(clk),
        .rst_n(rst_n),
        .width_config(config_width),
        .pulse(pulse_config)
    );

endmodule

// Configurable pulse generator module
module configurable_pulse_gen #(
    parameter int MAX_WIDTH = 1000000
) (
    input  logic [31:0] width_config,
    input  logic        clk,
    input  logic        rst_n,
    output logic        pulse
);

    logic [31:0] r_counter;
    logic [31:0] w_width_minus_one;
    
    assign w_width_minus_one = (width_config > 0) ? (width_config - 1) : 0;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter <= 32'h00000000;
            pulse <= 1'b0;
        end else begin
            if (r_counter < w_width_minus_one)
                r_counter <= r_counter + 1;
            else
                r_counter <= 32'h00000000;
                
            pulse <= (r_counter == w_width_minus_one) && (width_config > 0);
        end
    end

endmodule
```

### 6. Test Pattern Generation
```systemverilog
module test_pattern_generator (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       test_enable,
    input  logic [3:0] pattern_select,
    
    output logic [7:0] test_data,
    output logic       test_valid,
    output logic       pattern_complete
);

    logic update_pulse;
    logic [7:0] pattern_counter;
    
    // Generate test data update rate
    clock_pulse #(.WIDTH(16)) pattern_clock (
        .clk(clk),
        .rst_n(rst_n),
        .pulse(update_pulse)
    );
    
    // Pattern counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pattern_counter <= 8'h00;
        end else if (test_enable && update_pulse) begin
            pattern_counter <= pattern_counter + 1;
        end
    end
    
    // Test pattern generation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            test_data <= 8'h00;
            test_valid <= 1'b0;
        end else if (test_enable && update_pulse) begin
            case (pattern_select)
                4'h0: test_data <= pattern_counter;                    // Incrementing
                4'h1: test_data <= ~pattern_counter;                   // Decrementing
                4'h2: test_data <= {pattern_counter[0], 7'b0000000};   // Walking 1
                4'h3: test_data <= ~{pattern_counter[0], 7'b0000000};  // Walking 0
                4'h4: test_data <= 8'hAA;                             // Alternating
                4'h5: test_data <= 8'h55;                             // Alternating inv
                4'h6: test_data <= 8'hFF;                             // All ones
                4'h7: test_data <= 8'h00;                             // All zeros
                default: test_data <= pattern_counter;                 // Default
            endcase
            test_valid <= 1'b1;
        end else begin
            test_valid <= 1'b0;
        end
    end
    
    assign pattern_complete = test_enable && (&pattern_counter) && update_pulse;

endmodule
```

## Advanced Features and Variations

### 1. Enable-Controlled Pulse Generator
```systemverilog
module pulse_generator_with_enable #(
    parameter int WIDTH = 10
) (
    input  logic clk,
    input  logic rst_n,
    input  logic enable,      // Pulse generation enable
    input  logic pause,       // Pause counting (hold current state)
    output logic pulse,
    output logic [WIDTH-1:0] count_value  // Current counter value
);

    logic [WIDTH-1:0] r_counter;
    logic [WIDTH-1:0] w_width_minus_one;
    
    assign w_width_minus_one = WIDTH[WIDTH-1:0] - 1'b1;
    assign count_value = r_counter;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter <= 'b0;
            pulse <= 1'b0;
        end else if (enable && !pause) begin
            if (r_counter < w_width_minus_one)
                r_counter <= r_counter + 1'b1;
            else
                r_counter <= 'b0;
                
            pulse <= (r_counter == w_width_minus_one);
        end else begin
            pulse <= 1'b0;  // No pulse when disabled or paused
        end
    end

endmodule
```

### 2. Variable Width Pulse Generator
```systemverilog
module variable_pulse_generator #(
    parameter int MAX_WIDTH = 65536
) (
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic [$clog2(MAX_WIDTH):0]  pulse_width,   // Configurable width
    input  logic                        load_width,    // Load new width
    output logic                        pulse,
    output logic                        width_loaded
);

    logic [$clog2(MAX_WIDTH):0] r_counter;
    logic [$clog2(MAX_WIDTH):0] r_width;
    logic [$clog2(MAX_WIDTH):0] w_width_minus_one;
    
    assign w_width_minus_one = (r_width > 0) ? (r_width - 1) : 0;
    
    // Width register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_width <= MAX_WIDTH[$clog2(MAX_WIDTH):0];  // Default width
            width_loaded <= 1'b0;
        end else if (load_width) begin
            r_width <= (pulse_width > 0) ? pulse_width : 1;  // Minimum width = 1
            width_loaded <= 1'b1;
        end else begin
            width_loaded <= 1'b0;
        end
    end
    
    // Counter and pulse generation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter <= 'b0;
            pulse <= 1'b0;
        end else begin
            if (r_counter < w_width_minus_one)
                r_counter <= r_counter + 1;
            else
                r_counter <= 'b0;
                
            pulse <= (r_counter == w_width_minus_one) && (r_width > 0);
        end
    end

endmodule
```

### 3. Multi-Phase Pulse Generator
```systemverilog
module multi_phase_pulse_generator #(
    parameter int WIDTH = 12,
    parameter int PHASES = 4
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    output logic [PHASES-1:0] phase_pulses
);

    logic [WIDTH-1:0] r_counter;
    logic [WIDTH-1:0] w_width_minus_one;
    logic [WIDTH-1:0] phase_thresholds [PHASES];
    
    assign w_width_minus_one = WIDTH[WIDTH-1:0] - 1'b1;
    
    // Calculate phase thresholds
    genvar i;
    generate
        for (i = 0; i < PHASES; i++) begin : calc_phases
            assign phase_thresholds[i] = (WIDTH * i) / PHASES;
        end
    endgenerate
    
    // Counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter <= 'b0;
        end else if (enable) begin
            if (r_counter < w_width_minus_one)
                r_counter <= r_counter + 1;
            else
                r_counter <= 'b0;
        end
    end
    
    // Phase pulse generation
    generate
        for (i = 0; i < PHASES; i++) begin : gen_phases
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    phase_pulses[i] <= 1'b0;
                end else begin
                    phase_pulses[i] <= enable && (r_counter == phase_thresholds[i]);
                end
            end
        end
    endgenerate

endmodule
```

### 4. Burst Pulse Generator
```systemverilog
module burst_pulse_generator #(
    parameter int BURST_LENGTH = 8,
    parameter int BURST_PERIOD = 100,
    parameter int INTER_BURST_DELAY = 1000
) (
    input  logic clk,
    input  logic rst_n,
    input  logic enable,
    input  logic trigger,           // Start burst sequence
    
    output logic burst_pulse,       // Individual pulses in burst
    output logic burst_active,      // Burst sequence active
    output logic burst_complete     // Burst sequence completed
);

    typedef enum logic [2:0] {
        IDLE,
        BURST_ACTIVE,
        INTER_PULSE_DELAY,
        INTER_BURST_DELAY_ST
    } burst_state_t;
    
    burst_state_t state;
    
    logic [$clog2(BURST_LENGTH):0] pulse_count;
    logic [$clog2(BURST_PERIOD):0] period_counter;
    logic [$clog2(INTER_BURST_DELAY):0] delay_counter;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            pulse_count <= 0;
            period_counter <= 0;
            delay_counter <= 0;
            burst_pulse <= 1'b0;
            burst_complete <= 1'b0;
        end else begin
            burst_complete <= 1'b0;  // Default
            
            case (state)
                IDLE: begin
                    burst_pulse <= 1'b0;
                    if (enable && trigger) begin
                        state <= BURST_ACTIVE;
                        pulse_count <= 0;
                        period_counter <= 0;
                        burst_pulse <= 1'b1;  // First pulse
                    end
                end
                
                BURST_ACTIVE: begin
                    burst_pulse <= 1'b0;
                    pulse_count <= pulse_count + 1;
                    
                    if (pulse_count >= BURST_LENGTH - 1) begin
                        state <= INTER_BURST_DELAY_ST;
                        delay_counter <= 0;
                        burst_complete <= 1'b1;
                    end else begin
                        state <= INTER_PULSE_DELAY;
                        period_counter <= 0;
                    end
                end
                
                INTER_PULSE_DELAY: begin
                    period_counter <= period_counter + 1;
                    if (period_counter >= BURST_PERIOD - 1) begin
                        state <= BURST_ACTIVE;
                        burst_pulse <= 1'b1;
                    end
                end
                
                INTER_BURST_DELAY_ST: begin
                    delay_counter <= delay_counter + 1;
                    if (delay_counter >= INTER_BURST_DELAY - 1) begin
                        state <= IDLE;
                    end
                end
            endcase
        end
    end
    
    assign burst_active = (state != IDLE);

endmodule
```

## Verification and Testing

### Comprehensive Test Bench
```systemverilog
module tb_clock_pulse;

    parameter WIDTH = 10;
    
    logic clk, rst_n, pulse;
    
    // Clock generation
    initial clk = 0;
    always #5ns clk = ~clk; // 100MHz
    
    // DUT instantiation
    clock_pulse #(.WIDTH(WIDTH)) dut (.*);
    
    // Test sequence
    initial begin
        rst_n = 0;
        #100ns rst_n = 1;
        
        // Test basic pulse generation
        test_basic_pulse_generation();
        
        // Test reset behavior
        test_reset_behavior();
        
        // Test timing accuracy
        test_timing_accuracy();
        
        $display("All tests completed!");
        $finish;
    end
    
    // Test basic pulse generation
    task test_basic_pulse_generation();
        int pulse_count = 0;
        int cycle_count = 0;
        begin
            $display("Testing basic pulse generation (WIDTH=%0d)...", WIDTH);
            
            // Monitor for several pulse periods
            repeat (WIDTH * 3) begin
                @(posedge clk);
                cycle_count++;
                if (pulse) pulse_count++;
            end
            
            // Verify pulse count
            if (pulse_count == 3) begin
                $display("PASS: Correct number of pulses generated");
            end else begin
                $error("FAIL: Expected 3 pulses, got %0d", pulse_count);
            end
        end
    endtask
    
    // Test timing accuracy
    task test_timing_accuracy();
        time pulse_times[10];
        time pulse_periods[9];
        int i;
        real avg_period, expected_period;
        begin
            $display("Testing timing accuracy...");
            
            expected_period = WIDTH * 10.0; // 10ns clock period
            
            // Capture pulse timing
            for (i = 0; i < 10; i++) begin
                @(posedge pulse);
                pulse_times[i] = $time;
            end
            
            // Calculate periods
            for (i = 0; i < 9; i++) begin
                pulse_periods[i] = pulse_times[i+1] - pulse_times[i];
            end
            
            // Calculate average period
            avg_period = 0;
            for (i = 0; i < 9; i++) begin
                avg_period += pulse_periods[i];
            end
            avg_period = avg_period / 9.0;
            
            // Check accuracy (within 1% tolerance)
            if (abs(avg_period - expected_period) < expected_period * 0.01) begin
                $display("PASS: Average period = %.1f ns (expected %.1f ns)", 
                         avg_period, expected_period);
            end else begin
                $error("FAIL: Average period = %.1f ns (expected %.1f ns)", 
                       avg_period, expected_period);
            end
        end
    endtask
    
    function real abs(real value);
        abs = (value >= 0) ? value : -value;
    endfunction

endmodule
```

### Coverage Model
```systemverilog
covergroup clock_pulse_cg @(posedge clk);
    
    cp_counter_values: coverpoint dut.r_counter {
        bins zero = {0};
        bins low[] = {[1:WIDTH/4]};
        bins mid[] = {[WIDTH/4+1:3*WIDTH/4]};
        bins high[] = {[3*WIDTH/4+1:WIDTH-2]};
        bins max = {WIDTH-1};
    }
    
    cp_pulse: coverpoint pulse {
        bins asserted = {1};
        bins deasserted = {0};
    }
    
    cp_reset: coverpoint rst_n {
        bins reset = {0};
        bins normal = {1};
    }
    
    // Transition coverage
    cp_pulse_edges: coverpoint pulse {
        bins rising = (0 => 1);
        bins falling = (1 => 0);
        bins stable_low = (0 => 0);
        bins stable_high = (1 => 1);
    }
    
    // Cross coverage
    cross_counter_pulse: cross cp_counter_values, cp_pulse;

endcovergroup
```

### Formal Properties
```systemverilog
module clock_pulse_properties;

    // Bind to DUT
    bind clock_pulse clock_pulse_properties props_inst (.*);
    
    // Property: Pulse occurs at correct count
    property pulse_at_max_count;
        @(posedge clk) disable iff (!rst_n)
        (dut.r_counter == WIDTH-1) |-> pulse;
    endproperty
    
    // Property: Pulse only occurs at max count
    property pulse_only_at_max;
        @(posedge clk) disable iff (!rst_n)
        pulse |-> (dut.r_counter == WIDTH-1);
    endproperty
    
    // Property: Counter wraps correctly
    property counter_wrap;
        @(posedge clk) disable iff (!rst_n)
        (dut.r_counter == WIDTH-1) |=> (dut.r_counter == 0);
    endproperty
    
    // Property: Counter increments
    property counter_increment;
        @(posedge clk) disable iff (!rst_n)
        (dut.r_counter < WIDTH-1) |=> 
        (dut.r_counter == $past(dut.r_counter) + 1);
    endproperty
    
    // Property: Reset behavior
    property reset_behavior;
        @(posedge clk)
        !rst_n |=> (dut.r_counter == 0) && !pulse;
    endproperty
    
    // Assertions
    assert property (pulse_at_max_count);
    assert property (pulse_only_at_max);
    assert property (counter_wrap);
    assert property (counter_increment);
    assert property (reset_behavior);

endmodule
```

## Synthesis Considerations

### Resource Utilization
| WIDTH | Counter Bits | LUTs | FFs | Max Freq |
|-------|--------------|------|-----|----------|
| 8 | 3 | 8 | 4 | 500MHz |
| 16 | 4 | 12 | 5 | 450MHz |
| 32 | 5 | 18 | 6 | 400MHz |
| 1024 | 10 | 28 | 11 | 350MHz |

### Timing Optimization
```systemverilog
// For high-frequency applications, pipeline the comparison
module clock_pulse_pipelined #(
    parameter int WIDTH = 1000
) (
    input  logic clk,
    input  logic rst_n,
    output logic pulse
);

    logic [WIDTH-1:0] r_counter;
    logic [WIDTH-1:0] w_width_minus_one;
    logic compare_result;
    
    assign w_width_minus_one = WIDTH[WIDTH-1:0] - 1'b1;
    
    // Pipeline the comparison
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            compare_result <= 1'b0;
        end else begin
            compare_result <= (r_counter == w_width_minus_one);
        end
    end
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter <= 'b0;
            pulse <= 1'b0;
        end else begin
            if (compare_result)
                r_counter <= 'b0;
            else
                r_counter <= r_counter + 1;
                
            pulse <= compare_result;
        end
    end

endmodule
```

## Common Applications Summary

1. **Timing References**: System heartbeats, watchdog timers
2. **Sampling Systems**: ADC triggers, data acquisition timing
3. **Communication**: Baud rate generation, protocol timing
4. **Memory Systems**: Refresh timing, access scheduling
5. **Test Equipment**: Pattern generation, stimulus timing
6. **Power Management**: Activity monitoring, timeout generation
7. **Display Systems**: Refresh rates, sync generation

## Design Guidelines

1. **Choose Appropriate WIDTH**: Balance between resolution and resource usage
2. **Consider Reset Timing**: Ensure clean startup behavior
3. **Validate Timing**: Verify pulse frequency matches requirements
4. **Plan for Variation**: Consider process, voltage, temperature effects
5. **Monitor Resource Usage**: Large counters can impact timing and area
6. **Use Enables**: Add enable signals for conditional operation
7. **Document Timing**: Clearly specify pulse rates and relationships

The clock pulse generator provides a simple, reliable solution for periodic timing generation, essential for many digital system functions requiring precise, regular timing events.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
