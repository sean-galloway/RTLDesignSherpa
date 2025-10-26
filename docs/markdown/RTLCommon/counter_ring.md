# Ring Counter Module

## Overview
The `counter_ring` module implements a classic ring counter where a single '1' bit circulates through a shift register. This creates a one-hot encoded sequence that's ideal for generating sequential enable signals, creating walking LED patterns, or controlling multi-phase operations where only one stage should be active at a time.

## Module Declaration
```systemverilog
module counter_ring #(
    parameter int WIDTH = 4
) (
    input  wire             clk,
    input  wire             rst_n,
    input  wire             enable,
    output reg  [WIDTH-1:0] ring_out
);
```

## Parameters

### WIDTH
- **Type**: `int`
- **Default**: `4`
- **Description**: Number of stages in the ring counter
- **Range**: Any positive integer ≥ 1
- **States Generated**: WIDTH unique states
- **Pattern**: Single '1' bit rotates through WIDTH positions

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk` | 1 | `wire` | System clock input |
| `rst_n` | 1 | `wire` | Active-low asynchronous reset |
| `enable` | 1 | `wire` | Counter enable control |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `ring_out` | WIDTH | `reg` | Ring counter output (one-hot encoded) |

## Theory of Operation

### Ring Counter Principle
A ring counter is a circular shift register where:
- **Initialization**: Single '1' bit in LSB position
- **Operation**: The '1' bit rotates right each clock cycle
- **Feedback**: MSB connects back to LSB (no inversion)
- **States**: WIDTH unique one-hot states

### Mathematical Representation
For each clock cycle when enabled:
```
ring_out[i] = ring_out[i-1]  for i = 1 to WIDTH-1
ring_out[0] = ring_out[WIDTH-1]
```

## Implementation Details

### Core Logic
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        ring_out <= 'b1;  // Initialize with LSB set
    end else if (enable) begin
        // Right rotate operation
        ring_out <= {ring_out[0], ring_out[WIDTH-1:1]};
    end
end
```

### Operation Breakdown
1. **Reset State**: `ring_out = 'b1` (only LSB set)
2. **Rotation**: `{ring_out[0], ring_out[WIDTH-1:1]}`
   - MSB becomes new LSB
   - All other bits shift right
3. **Enable Control**: Only advances when `enable` is high
4. **Circular**: After WIDTH cycles, returns to initial state

## State Sequences

### 4-bit Ring Counter (WIDTH=4)
| Step | ring_out | Binary | One-Hot Position |
|------|----------|--------|------------------|
| 0 | 0001 | Reset state | Position 0 active |
| 1 | 1000 | After 1 clock | Position 3 active |
| 2 | 0100 | After 2 clocks | Position 2 active |
| 3 | 0010 | After 3 clocks | Position 1 active |
| 4 | 0001 | After 4 clocks | Back to start |

### 3-bit Ring Counter (WIDTH=3)
| Step | ring_out | Active Stage |
|------|----------|--------------|
| 0 | 001 | Stage 0 |
| 1 | 100 | Stage 2 |
| 2 | 010 | Stage 1 |
| 3 | 001 | Stage 0 (repeat) |

### 8-bit Ring Counter Example
```
Step 0: 00000001 (Stage 0)
Step 1: 10000000 (Stage 7)  
Step 2: 01000000 (Stage 6)
Step 3: 00100000 (Stage 5)
Step 4: 00010000 (Stage 4)
Step 5: 00001000 (Stage 3)
Step 6: 00000100 (Stage 2)
Step 7: 00000010 (Stage 1)
Step 8: 00000001 (Stage 0) - Cycle repeats
```

## Design Examples

### 1. Sequential Enable Generator
```systemverilog
counter_ring #(
    .WIDTH(4)
) seq_enable (
    .clk(clk),
    .rst_n(rst_n),
    .enable(sequence_active),
    .ring_out(stage_enables)
);

// Use each bit as an enable for different stages
assign stage0_enable = stage_enables[0];
assign stage1_enable = stage_enables[1];
assign stage2_enable = stage_enables[2];
assign stage3_enable = stage_enables[3];

// Example: Pipeline stage control
always_ff @(posedge clk) begin
    if (stage0_enable) stage0_data <= input_data;
    if (stage1_enable) stage1_data <= process_stage0(stage0_data);
    if (stage2_enable) stage2_data <= process_stage1(stage1_data);
    if (stage3_enable) output_data <= process_stage2(stage2_data);
end
```

### 2. LED Chaser Display
```systemverilog
// Create walking LED pattern
counter_ring #(
    .WIDTH(8)
) led_chaser (
    .clk(slow_clk),          // ~2Hz for visible effect
    .rst_n(rst_n),
    .enable(chase_enabled),
    .ring_out(led_pattern)
);

// Connect directly to LEDs
assign leds[7:0] = led_pattern;

// Optional: Bidirectional chaser
logic direction;
logic [7:0] led_display;

always_comb begin
    if (direction)
        led_display = led_pattern;
    else
        led_display = {led_pattern[0], led_pattern[7:1]}; // Reverse
end
```

### 3. Memory Bank Sequencer
```systemverilog
counter_ring #(
    .WIDTH(4)
) bank_sequencer (
    .clk(clk),
    .rst_n(rst_n),
    .enable(memory_active),
    .ring_out(bank_select)
);

// Memory bank control
logic [3:0] bank_cs_n;
assign bank_cs_n = ~bank_select;  // Active low chip selects

// Example: Round-robin memory access
always_comb begin
    mem_addr = base_addr;
    mem_data_out = 32'h0;
    
    case (bank_select)
        4'b0001: begin
            mem_addr = bank0_addr;
            mem_data_out = bank0_data;
        end
        4'b0010: begin
            mem_addr = bank1_addr;
            mem_data_out = bank1_data;
        end
        4'b0100: begin
            mem_addr = bank2_addr;
            mem_data_out = bank2_data;
        end
        4'b1000: begin
            mem_addr = bank3_addr;
            mem_data_out = bank3_data;
        end
    endcase
end
```

### 4. State Machine Controller
```systemverilog
// Simple state machine using ring counter
counter_ring #(
    .WIDTH(5)
) state_machine (
    .clk(clk),
    .rst_n(rst_n),
    .enable(state_advance),
    .ring_out(current_state)
);

// Decode states
assign state_idle    = current_state[0];
assign state_request = current_state[1];
assign state_wait    = current_state[2];
assign state_active  = current_state[3];
assign state_done    = current_state[4];

// State machine logic
always_ff @(posedge clk) begin
    case (1'b1)  // One-hot case statement
        state_idle:    state_advance <= start_request;
        state_request: state_advance <= request_granted;
        state_wait:    state_advance <= ready_signal;
        state_active:  state_advance <= operation_complete;
        state_done:    state_advance <= 1'b1;  // Always advance from done
        default:       state_advance <= 1'b0;
    endcase
end
```

### 5. Clock Domain Multiplexer
```systemverilog
// Sequentially select different clock domains
counter_ring #(
    .WIDTH(3)
) clk_mux_ctrl (
    .clk(control_clk),
    .rst_n(rst_n),
    .enable(mux_advance),
    .ring_out(clk_select)
);

// Clock multiplexer (use proper clock muxing in real design)
logic selected_clk;
always_comb begin
    case (clk_select)
        3'b001: selected_clk = clk_domain_0;
        3'b010: selected_clk = clk_domain_1;
        3'b100: selected_clk = clk_domain_2;
        default: selected_clk = 1'b0;
    endcase
end
```

## Properties and Characteristics

### One-Hot Encoding
Ring counters naturally provide one-hot encoding:
- **Exactly One Bit Set**: Always exactly one bit is '1'
- **Unique States**: Each state is distinctly different
- **Easy Decode**: No additional decoding logic needed
- **Glitch-Free**: Clean transitions between states

### Self-Correcting Behavior
Ring counters have some self-correcting properties:
- **All Zeros**: Will remain stuck (not self-correcting)
- **Multiple Ones**: Will maintain multiple bits indefinitely
- **Single One**: Will operate correctly

### Comparison with Other Counters

| Counter Type | States | Decode Logic | One-Hot | Power |
|--------------|--------|--------------|---------|-------|
| Binary | 2^N | Complex | No | Low |
| Gray | 2^N | Moderate | No | Low |
| Johnson | 2×N | Moderate | No | Low |
| Ring | N | None | Yes | Medium |

## Advanced Usage

### 1. Self-Correcting Ring Counter
```systemverilog
// Add error correction for stuck states
logic error_detected;
logic [WIDTH-1:0] corrected_ring;

assign error_detected = (ring_out == 'b0) || ($countones(ring_out) != 1);

always_comb begin
    if (error_detected)
        corrected_ring = 'b1;  // Force to valid state
    else
        corrected_ring = ring_out;
end
```

### 2. Bidirectional Ring Counter
```systemverilog
logic direction;  // 0 = right, 1 = left

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        ring_out <= 'b1;
    end else if (enable) begin
        if (direction)
            // Left rotate
            ring_out <= {ring_out[WIDTH-2:0], ring_out[WIDTH-1]};
        else
            // Right rotate  
            ring_out <= {ring_out[0], ring_out[WIDTH-1:1]};
    end
end
```

### 3. Programmable Ring Counter
```systemverilog
logic [WIDTH-1:0] init_pattern;
logic load_pattern;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        ring_out <= 'b1;
    end else if (load_pattern) begin
        ring_out <= init_pattern;
    end else if (enable) begin
        ring_out <= {ring_out[0], ring_out[WIDTH-1:1]};
    end
end
```

## Verification Strategy

### Test Scenarios
1. **Reset Behavior**: Verify initialization to single '1' bit
2. **Rotation Sequence**: Check complete WIDTH-step cycle
3. **Enable Control**: Test hold behavior when disabled
4. **One-Hot Property**: Ensure exactly one bit set always
5. **Cycle Completion**: Verify return to initial state

### Coverage Model
```systemverilog
covergroup ring_cg @(posedge clk);
    cp_ring_state: coverpoint ring_out {
        bins valid_states[] = {1, 2, 4, 8, 16, 32, 64, 128}; // For WIDTH=8
        bins invalid_states[] = default;
    }
    
    cp_enable: coverpoint enable {
        bins enabled = {1};
        bins disabled = {0};
    }
    
    cp_one_hot: coverpoint $countones(ring_out) {
        bins exactly_one = {1};
        bins zero = {0};
        bins multiple = {[2:WIDTH]};
    }
    
    // Verify complete cycle
    cp_transitions: coverpoint ring_out {
        bins cycle[] = (1 => 8), (8 => 4), (4 => 2), (2 => 1); // For WIDTH=4
    }
endgroup
```

### Assertions
```systemverilog
// Exactly one bit should be set (except during reset)
property one_hot_property;
    @(posedge clk) disable iff (!rst_n)
    $countones(ring_out) == 1;
endproperty

// After reset, should start with LSB set
property reset_state;
    @(posedge clk)
    $rose(rst_n) |-> ring_out == 1;
endproperty

// When enabled, should rotate right
property rotation_property;
    @(posedge clk) disable iff (!rst_n)
    enable |=> ring_out == {$past(ring_out[0]), $past(ring_out[WIDTH-1:1])};
endproperty

assert property (one_hot_property);
assert property (reset_state);
assert property (rotation_property);
```

## Synthesis Considerations

### Resource Utilization
- **Flip-Flops**: WIDTH registers
- **LUTs**: Minimal - just shift logic
- **Routing**: Simple interconnections

### Optimization Tips
```systemverilog
// Use SRL (Shift Register LUT) inference when appropriate
(* SRL_STYLE = "register" *) reg [WIDTH-1:0] ring_out;

// For very wide counters, consider using dedicated shift register primitives
```

### Timing Considerations
- **Clock Skew**: Ensure clean clock distribution
- **Setup/Hold**: Standard flip-flop requirements
- **Routing Delay**: Minimal due to simple structure

## Performance Characteristics

### Maximum Frequency
- **Typical**: 400-600 MHz in modern FPGAs
- **Limitation**: Shift register timing
- **Advantage**: Very simple logic path

### Power Consumption
- **Dynamic**: Proportional to switching frequency
- **Optimization**: Higher switching than binary counters
- **Trade-off**: Simplicity vs. power efficiency

## Common Pitfalls

### 1. Invalid Initial States
```systemverilog
// Problem: Multiple bits set
ring_out <= 4'b1001;  // Invalid - two bits set

// Solution: Use proper initialization
ring_out <= 4'b0001;  // Valid - exactly one bit
```

### 2. Stuck at Zero
```systemverilog
// Problem: All zeros state
if (ring_out == 'b0) begin
    ring_out <= 'b1;  // Force recovery
end
```

### 3. Width Mismatch
```systemverilog
// Problem: Initialization doesn't match width
parameter WIDTH = 8;
ring_out <= 4'b0001;  // Wrong - should be 8'b00000001

// Solution: Use proper width
ring_out <= 'b1;      // Correct - sized automatically
```

## Related Modules
- `counter_johnson`: Twisted-ring counter with 2×WIDTH states
- `counter_bingray`: Binary/Gray counter for different applications
- Standard shift register implementations
- One-hot state machines

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
