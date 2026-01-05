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

# Johnson Counter Module

## Overview
The `counter_johnson` module implements a Johnson counter (also known as a twisted-ring counter or switch-tail counter). This is a special type of shift register where the inverted output of the last stage is fed back to the first stage, creating a sequence with 2×WIDTH unique states. Johnson counters are widely used for generating multi-phase clock signals, state machine control, and sequential timing applications.

## Module Declaration
```systemverilog
module counter_johnson #(
    parameter int WIDTH = 4
) (
    input  logic                clk,
    input  logic                rst_n,
    input  logic                enable,
    output logic [WIDTH - 1:0]  counter_gray
);
```

## Parameters

### WIDTH
- **Type**: `int`
- **Default**: `4`
- **Description**: Number of stages in the Johnson counter
- **Range**: Any positive integer ≥ 1
- **States Generated**: 2×WIDTH unique states
- **Impact**: Determines sequence length and number of output phases

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk` | 1 | `logic` | System clock input |
| `rst_n` | 1 | `logic` | Active-low asynchronous reset |
| `enable` | 1 | `logic` | Counter enable control |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `counter_gray` | WIDTH | `logic` | Johnson counter output register |

## Theory of Operation

### Johnson Counter Principle
A Johnson counter is a shift register with inverted feedback:
- **Normal Operation**: Bits shift left (or right) each clock cycle
- **Feedback**: The complement of the MSB feeds back to the LSB
- **Sequence Length**: 2×WIDTH states before repeating

### Mathematical Representation
For a WIDTH-bit Johnson counter:
```
Next_State[i] = Current_State[i-1]  for i = 1 to WIDTH-1
Next_State[0] = ~Current_State[WIDTH-1]
```

## Implementation Details

### Core Logic
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) 
        counter_gray <= {WIDTH{1'b0}};  // Reset to all zeros
    else if (enable) begin
        counter_gray <= {counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]};
    end
end
```

### Operation Breakdown
1. **Shift Operation**: `counter_gray[WIDTH-2:0]` → lower bits of next state
2. **Feedback**: `~counter_gray[WIDTH-1]` → MSB complement becomes new LSB
3. **Enable Control**: Only advance when `enable` is asserted
4. **Reset**: All bits cleared on reset

## State Sequences

### 4-bit Johnson Counter (WIDTH=4)
| Step | counter_gray | Decimal | Description |
|------|--------------|---------|-------------|
| 0 | 0000 | 0 | Reset state |
| 1 | 0001 | 1 | First '1' enters |
| 2 | 0011 | 3 | '1' propagates |
| 3 | 0111 | 7 | '1' propagates |
| 4 | 1111 | 15 | All '1's |
| 5 | 1110 | 14 | First '0' enters |
| 6 | 1100 | 12 | '0' propagates |
| 7 | 1000 | 8 | '0' propagates |
| 8 | 0000 | 0 | Back to start |

### 3-bit Johnson Counter (WIDTH=3)
| Step | counter_gray | Binary Pattern |
|------|--------------|----------------|
| 0 | 000 | All zeros |
| 1 | 001 | One bit set |
| 2 | 011 | Two bits set |
| 3 | 111 | All ones |
| 4 | 110 | Two bits set |
| 5 | 100 | One bit set |
| 6 | 000 | Cycle repeats |

### 2-bit Johnson Counter (WIDTH=2)
| Step | counter_gray | State Name |
|------|--------------|------------|
| 0 | 00 | State A |
| 1 | 01 | State B |
| 2 | 11 | State C |
| 3 | 10 | State D |
| 4 | 00 | Back to A |

## Unique Properties

### Self-Starting
Johnson counters are self-starting from most invalid states:
- **Valid States**: 2×WIDTH states in the normal sequence
- **Invalid States**: (2^WIDTH - 2×WIDTH) states not in sequence
- **Recovery**: Most invalid states naturally converge to valid sequence

### Symmetrical Patterns
The sequence has inherent symmetry:
- **First Half**: Filling with '1's (0→1→11→111...)
- **Second Half**: Filling with '0's (111→110→100→000...)
- **Phase Shift**: Each bit represents a different phase

### Gray Code Properties
Johnson counter outputs have some Gray code characteristics:
- **Adjacent Differences**: States differ by more than one bit
- **Predictable Transitions**: Well-defined state progression
- **Decode Simplicity**: Easy to decode specific states

## Design Examples

### 1. 4-Phase Clock Generator
```systemverilog
counter_johnson #(
    .WIDTH(4)
) phase_gen (
    .clk(master_clk),
    .rst_n(rst_n),
    .enable(1'b1),
    .counter_gray(phases)
);

// Decode individual phases
assign phase_0 = (phases == 4'b0001);  // Step 1
assign phase_1 = (phases == 4'b0011);  // Step 2  
assign phase_2 = (phases == 4'b0111);  // Step 3
assign phase_3 = (phases == 4'b1111);  // Step 4
```

### 2. LED Chaser Effect
```systemverilog
counter_johnson #(
    .WIDTH(8)
) led_chaser (
    .clk(slow_clk),        // ~1Hz clock
    .rst_n(rst_n),
    .enable(chase_enable),
    .counter_gray(led_pattern)
);

// LEDs show walking pattern
assign leds[7:0] = led_pattern;
```

### 3. State Machine Controller
```systemverilog
counter_johnson #(
    .WIDTH(3)
) state_ctrl (
    .clk(clk),
    .rst_n(rst_n), 
    .enable(state_advance),
    .counter_gray(state_code)
);

// Decode states for control logic
always_comb begin
    case (state_code)
        3'b001: current_state = INIT;
        3'b011: current_state = LOAD;
        3'b111: current_state = PROCESS;
        3'b110: current_state = STORE;
        3'b100: current_state = CLEANUP;
        3'b000: current_state = IDLE;
        default: current_state = ERROR;
    endcase
end
```

### 4. Quadrature Signal Generation
```systemverilog
// Generate quadrature encoder-like signals
counter_johnson #(
    .WIDTH(4)
) quad_gen (
    .clk(position_clk),
    .rst_n(rst_n),
    .enable(motor_moving),
    .counter_gray(quad_state)
);

// Extract A and B channels with 90° phase shift
assign quad_a = quad_state[0] ^ quad_state[1];
assign quad_b = quad_state[1] ^ quad_state[2];
```

## Advantages

### 1. Simplicity
- **Minimal Logic**: Just a shift register with inverted feedback
- **No Decode Logic**: States can be used directly
- **Self-Clocking**: No complex timing requirements

### 2. Reliability
- **Self-Starting**: Recovers from most error states
- **No Invalid States**: All reachable states are functional
- **Glitch-Free**: Clean transitions between states

### 3. Performance
- **High Speed**: Simple logic allows high clock frequencies
- **Low Power**: Minimal switching activity
- **Predictable Timing**: Regular state progression

### 4. Flexibility
- **Scalable**: Any width supported
- **Multiple Outputs**: Each bit provides different phase
- **Easy Modification**: Simple parameter changes

## Disadvantages

### 1. Limited States
- **Count Efficiency**: Only 2×WIDTH states vs 2^WIDTH for binary
- **Sequence Constraint**: Fixed progression pattern
- **No Random Access**: Must step through sequence

### 2. Decode Complexity
- **State Detection**: May need comparators for specific states
- **Non-Binary**: Not directly compatible with binary logic
- **Overlap Prevention**: Care needed to avoid state conflicts

## Applications

### Clock Generation
```systemverilog
// Multi-phase clock for pipeline stages
counter_johnson #(.WIDTH(4)) pipeline_phases (
    .clk(master_clk),
    .enable(pipeline_enable),
    .counter_gray(phase_vector)
);

// Generate phase-shifted clocks
assign clk_ph0 = master_clk & phase_vector[0];
assign clk_ph1 = master_clk & phase_vector[1];
assign clk_ph2 = master_clk & phase_vector[2];
assign clk_ph3 = master_clk & phase_vector[3];
```

### Sequential Control
```systemverilog
// Memory refresh controller
counter_johnson #(.WIDTH(3)) refresh_ctrl (
    .clk(clk),
    .enable(refresh_request),
    .counter_gray(refresh_phase)
);

// Control refresh operations
assign precharge = (refresh_phase == 3'b001);
assign activate  = (refresh_phase == 3'b011);
assign refresh   = (refresh_phase == 3'b111);
assign restore   = (refresh_phase == 3'b110);
```

### Pattern Generation
```systemverilog
// Test pattern generator
counter_johnson #(.WIDTH(8)) pattern_gen (
    .clk(test_clk),
    .enable(pattern_enable), 
    .counter_gray(test_pattern)
);

// Use for built-in self-test (BIST)
assign test_data = test_pattern;
```

## Verification Strategy

### Functional Tests
1. **Sequence Verification**: Check complete 2×WIDTH state cycle
2. **Reset Behavior**: Verify initialization to all zeros
3. **Enable Control**: Test hold behavior when disabled
4. **Self-Starting**: Verify recovery from invalid states

### Coverage Points
```systemverilog
covergroup johnson_cg @(posedge clk);
    cp_states: coverpoint counter_gray {
        // Valid Johnson counter states for WIDTH=4
        bins valid_states[] = {4'b0000, 4'b0001, 4'b0011, 4'b0111,
                              4'b1111, 4'b1110, 4'b1100, 4'b1000};
        bins invalid_states[] = default;
    }
    
    cp_transitions: coverpoint counter_gray {
        bins valid_trans[] = (4'b0000 => 4'b0001),
                            (4'b0001 => 4'b0011),
                            (4'b0011 => 4'b0111),
                            (4'b0111 => 4'b1111),
                            (4'b1111 => 4'b1110),
                            (4'b1110 => 4'b1100),
                            (4'b1100 => 4'b1000),
                            (4'b1000 => 4'b0000);
    }
    
    cp_enable: coverpoint enable {
        bins enabled = {1};
        bins disabled = {0};
    }
endgroup
```

### Assertions
```systemverilog
// Verify valid state progression
property johnson_sequence;
    @(posedge clk) disable iff (!rst_n)
    enable && (counter_gray == 4'b0000) |=> 
    counter_gray == 4'b0001;
endproperty

assert property (johnson_sequence);

// Check for invalid states
property no_invalid_states;
    @(posedge clk) disable iff (!rst_n)
    counter_gray inside {4'b0000, 4'b0001, 4'b0011, 4'b0111,
                        4'b1111, 4'b1110, 4'b1100, 4'b1000};
endproperty

assert property (no_invalid_states);
```

## Synthesis Considerations

### Resource Utilization
- **Flip-Flops**: WIDTH registers
- **LUTs**: Minimal - just for shift and invert logic
- **Routing**: Simple connections between adjacent stages

### Optimization
```systemverilog
// For high-speed applications, consider pipeline stages
logic [WIDTH-1:0] johnson_pipe;
always_ff @(posedge clk) begin
    johnson_pipe <= {counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]};
end
```

### Tool Attributes
```systemverilog
(* SHREG_EXTRACT = "NO" *) logic [WIDTH-1:0] counter_gray; // Prevent SRL inference
```

## Performance Characteristics

### Maximum Frequency
- **Typical**: 400-600 MHz in modern FPGAs
- **Limitation**: Shift register timing
- **Optimization**: Pipeline for extreme speeds

### Power Consumption
- **Low Dynamic Power**: Only one bit changes per cycle
- **Efficient**: Minimal logic switching
- **Clock Gating**: Use enable for power savings

## WaveDrom Visualization

**High-quality waveforms showcasing Johnson counter operation are available!**

The following timing diagrams demonstrate the unique properties of Johnson counters across 4 key scenarios:

### Scenario 1: Walking Ones and Walking Zeros Pattern

![Johnson Walking Pattern](../../assets/WAVES/counter_johnson/johnson_counter_walking_pattern.png)

**WaveJSON:** [johnson_counter_walking_pattern.json](../../assets/WAVES/counter_johnson/johnson_counter_walking_pattern.json)

Complete 2×WIDTH state cycle (8 states for WIDTH=4):
- Walking ones: 0000 → 0001 → 0011 → 0111 → 1111
- Walking zeros: 1111 → 1110 → 1100 → 1000 → 0000
- Demonstrates predictable sequential progression

### Scenario 2: Single-Bit Transitions (CDC Safety) ⭐ **KEY FEATURE**

![Johnson Single-Bit Transitions](../../assets/WAVES/counter_johnson/johnson_counter_single_bit_transitions.png)

**WaveJSON:** [johnson_counter_single_bit_transitions.json](../../assets/WAVES/counter_johnson/johnson_counter_single_bit_transitions.json)

Each transition changes only ONE bit:
- CDC-safe like Gray codes
- **Critical for fifo_async_div2 CDC mechanism**
- Prevents metastability in clock domain crossing
- Hamming distance = 1 between all adjacent states

### Scenario 3: Enable Control

![Johnson Enable Control](../../assets/WAVES/counter_johnson/johnson_counter_enable_control.png)

**WaveJSON:** [johnson_counter_enable_control.json](../../assets/WAVES/counter_johnson/johnson_counter_enable_control.json)

Enable control and state holding:
- Counter advances when enable=1
- Counter holds state when enable=0
- Clean enable/disable transitions
- Demonstrates conditional counting

### Scenario 4: Reset Behavior

![Johnson Reset Behavior](../../assets/WAVES/counter_johnson/johnson_counter_reset_behavior.png)

**WaveJSON:** [johnson_counter_reset_behavior.json](../../assets/WAVES/counter_johnson/johnson_counter_reset_behavior.json)

Reset and initialization:
- Asynchronous reset to all zeros (0000)
- Immediate reset effect
- Clean restart from reset state
- Reset during counting operation

---

**To regenerate these waveforms:**
```bash
pytest val/common/test_counter_johnson_wavedrom.py -v
# Then convert JSON to PNG:
cd docs/markdown/assets/WAVES/counter_johnson
for f in *.json; do wavedrom-cli -i "$f" -p "${f%.json}.png"; done
```

**What Makes Johnson Counters Special:**

The waveforms highlight the unique properties that make Johnson counters useful:
- **Single-Bit Transitions**: Only one bit changes per state, making them CDC-safe
- **2×WIDTH States**: More efficient than one-hot (N states with N/2 flip-flops)
- **Walking Pattern**: Natural "fill then empty" sequence useful for visual effects
- **Self-Starting**: Recovers from invalid states automatically

**Relationship to fifo_async_div2:**

Johnson counters are the foundation of the `fifo_async_div2` CDC mechanism:
- **fifo_async_div2** uses Johnson counters for pointer synchronization
- Single-bit transitions enable safe clock domain crossing
- Linear width scaling (DEPTH bits) allows flexible even depths
- See `test_fifo_async_div2_wavedrom.py` for CDC application

**Comparison with Other Counters:**

- `test_counter_bingray_wavedrom.py` - Binary-Gray counter (power-of-2 depths, logarithmic width)
- `test_fifo_async_wavedrom.py` - Gray code in action (async FIFO)
- `test_fifo_async_div2_wavedrom.py` - Johnson counter in action (async FIFO, even depths)

## Related Modules
- `counter_ring`: Different shift register pattern
- `counter_bingray`: Binary and Gray code counter
- `counter`: Simple binary counter
- Standard shift register implementations

## Test and Verification

**Comprehensive Test Suite:**
- `val/common/test_counter_johnson.py` - Full functional verification
- `val/common/test_counter_johnson_wavedrom.py` - WaveDrom timing diagrams ⭐

**Run Tests:**
```bash
# Full functional test (basic/medium/full levels)
pytest val/common/test_counter_johnson.py -v

# WaveDrom waveform generation
pytest val/common/test_counter_johnson_wavedrom.py -v
```

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
