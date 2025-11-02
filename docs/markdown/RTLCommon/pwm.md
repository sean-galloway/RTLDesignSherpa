# PWM (Pulse Width Modulation) Module

## Purpose
The PWM module generates multiple independent pulse width modulation signals with configurable duty cycles, periods, and repeat counts. Each channel operates as an independent state machine with precise timing control and completion detection.

## Key Features
- Multiple independent PWM channels (parameterizable)
- Individual duty cycle, period, and repeat count control per channel
- Edge-triggered start control with automatic edge detection
- Completion status reporting per channel
- Support for continuous operation (infinite repeat)
- Precise timing with configurable counter width

## Port Description

### Parameters
- **WIDTH**: Bit width of counters and timing parameters (default: 8)
- **CHANNELS**: Number of independent PWM channels (default: 4)

### Inputs
| Port | Width | Description |
|------|-------|-------------|
| `clk` | 1 | System clock |
| `rst_n` | 1 | Active-low asynchronous reset |
| `start` | CHANNELS | Start trigger for each channel (edge-triggered) |
| `duty` | CHANNELS*WIDTH | Concatenated duty cycle values for all channels |
| `period` | CHANNELS*WIDTH | Concatenated period values for all channels |
| `repeat_count` | CHANNELS*WIDTH | Concatenated repeat counts (0 = infinite) |

### Outputs
| Port | Width | Description |
|------|-------|-------------|
| `done` | CHANNELS | Completion status for each channel |
| `pwm_out` | CHANNELS | PWM output signals for each channels |

## State Machine

Each PWM channel implements a 3-state finite state machine:

### States
```systemverilog
typedef enum logic [1:0] {
    IDLE = 2'b00,     // Waiting for start trigger
    RUNNING = 2'b01,  // Actively generating PWM
    DONE = 2'b10      // Completed all repeats
} state_t;
```

### State Transitions

#### IDLE → RUNNING
- **Condition**: `w_start_edge && local_period > 0`
- **Action**: Reset counters and begin PWM generation

#### RUNNING → DONE  
- **Condition**: `w_period_complete && w_all_repeats_done`
- **Action**: Stop PWM generation and assert done flag

#### DONE → RUNNING
- **Condition**: `w_start_edge`
- **Action**: Restart PWM generation with reset counters

#### Any State → IDLE
- **Condition**: System reset
- **Action**: Initialize all registers

## Implementation Details

### Per-Channel Parameter Extraction
```systemverilog
localparam int EndIdx = (i + 1) * WIDTH - 1;
assign local_duty = duty[EndIdx-:WIDTH];
assign local_period = period[EndIdx-:WIDTH];
assign local_repeat = repeat_count[EndIdx-:WIDTH];
```

### Edge Detection for Start Signal
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) r_start_prev <= 1'b0;
    else r_start_prev <= start[i];
end
assign w_start_edge = start[i] && !r_start_prev;
```

### PWM Output Generation Logic
```systemverilog
always_comb begin
    case (r_state)
        RUNNING: begin
            if (local_duty == 0) begin
                // 0% duty cycle
                pwm_out[i] = 1'b0;
            end else if (local_duty >= local_period) begin
                // 100% duty cycle (duty >= period)
                pwm_out[i] = 1'b1;
            end else begin
                // Normal case: PWM high for first 'duty' cycles
                pwm_out[i] = (r_count < local_duty);
            end
        end
        default: begin
            pwm_out[i] = 1'b0;
        end
    endcase
end
```

### Counter Management

#### Main Counter (Period Timing)
- Increments each clock cycle during RUNNING state
- Resets to 0 when reaching `local_period - 1`
- Controls PWM frequency

#### Repeat Counter
- Increments each time a period completes
- Compared against `repeat_count` to determine completion
- Special case: `repeat_count == 0` means infinite operation

### Critical Control Signals

#### Period Completion Detection
```systemverilog
assign w_period_complete = (r_count == local_period - 1) && (r_state == RUNNING);
```

#### All Repeats Done Detection  
```systemverilog
assign w_all_repeats_done = (local_repeat == 0) ? 1'b0 :  // 0 means infinite
                            (r_repeat_value >= local_repeat);
```

## Special Implementation Notes

### 1. Edge-Triggered Start Control
- Prevents continuous restart while start signal is held high
- Enables precise control of PWM initiation
- Each channel has independent edge detection

### 2. Duty Cycle Edge Cases
- **0% Duty**: Output permanently low during RUNNING state
- **100% Duty**: Output permanently high when `duty >= period`
- **Normal Operation**: High for first `duty` clock cycles of each period

### 3. Infinite Repeat Mode
- `repeat_count = 0` enables continuous operation
- PWM runs indefinitely until new start trigger
- Useful for continuous motor control or LED dimming

### 4. Simultaneous Multi-Channel Operation
- All channels operate independently
- No inter-channel dependencies or conflicts
- Scalable to any number of channels via parameters

### 5. Reset Behavior
- Asynchronous reset immediately stops all PWM outputs
- All internal counters and state machines reset to IDLE
- Clean startup guaranteed after reset deassertion

## Timing Examples

### Single Period Example (WIDTH=8, duty=3, period=8)
```
Clock:  0 1 2 3 4 5 6 7 0 1 2 3 4 5 6 7 ...
Count:  0 1 2 3 4 5 6 7 0 1 2 3 4 5 6 7 ...
PWM:    1 1 1 0 0 0 0 0 1 1 1 0 0 0 0 0 ...
```

### Multi-Repeat Example (repeat_count=2)
```
Period: 1     2     DONE
PWM:    ████▒▒▒▒████▒▒▒▒____
```

## Usage Scenarios

### Motor Speed Control
```systemverilog
// 50% duty cycle, 1kHz frequency (assuming 1MHz clock)
duty = 500;
period = 1000; 
repeat_count = 0;  // Continuous operation
```

### LED Dimming Sequence
```systemverilog
// Fade effect with 10 brightness levels
duty = brightness_level * 10;
period = 100;
repeat_count = fade_duration;
```

### Servo Motor Control
```systemverilog
// 20ms period with 1-2ms pulse width
duty = servo_position;     // 1000-2000 for 1-2ms
period = 20000;           // 20ms at 1MHz clock  
repeat_count = 1;         // Single pulse
```

## Applications
- Motor speed control
- LED brightness control
- Servo motor positioning
- Audio signal generation
- Power supply switching
- Heating element control

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
