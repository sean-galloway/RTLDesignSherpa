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

# Debounce Module (`debounce.sv`)

## Purpose
Eliminates mechanical switch bounce by sampling button inputs at regular intervals and requiring a stable state for multiple consecutive samples before considering the button state as valid.

## Ports

### Input Ports
- **`clk`** - System clock signal
- **`rst_n`** - Active-low reset signal  
- **`long_tick`** - ~10ms sampling tick signal (controls sampling rate)
- **`button_in[N-1:0]`** - Raw button input signals to be debounced

### Output Ports
- **`button_out[N-1:0]`** - Debounced button output signals

### Parameters
- **`N`** - Number of buttons/input signals (default: 4)
- **`DEBOUNCE_DELAY`** - Number of consecutive stable samples required (default: 4)
- **`PRESSED_STATE`** - Logic level when button is pressed (1 for normally open, 0 for normally closed)

## Implementation Details

### Core Algorithm
The module uses shift registers to track the history of each button's state:

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        for (int i = 0; i < N; i++) begin
            r_shift_regs[i] <= {DEBOUNCE_DELAY{1'b0}};
        end
    end else if (long_tick) begin
        for (int i = 0; i < N; i++) begin
            r_shift_regs[i] <= {
                r_shift_regs[i][DEBOUNCE_DELAY-2:0], 
                PRESSED_STATE ? button_in[i] : ~button_in[i]
            };
        end
    end
end
```

### Key Features

#### Sampling Control
- Only samples inputs when `long_tick` is asserted
- Prevents over-sampling which could cause false triggering
- Typical `long_tick` period: ~10ms

#### Button Type Support
- **Normally Open (NO)**: `PRESSED_STATE = 1`
  - Button reads '0' when not pressed, '1' when pressed
- **Normally Closed (NC)**: `PRESSED_STATE = 0`  
  - Button reads '1' when not pressed, '0' when pressed
- Input inversion handles NC buttons transparently

#### Debounce Logic
- Maintains `DEBOUNCE_DELAY` samples for each button
- Output goes high only when all samples in shift register are '1'
- This ensures the button has been stable in pressed state for required duration

```systemverilog
always_comb begin
    for (int i = 0; i < N; i++) begin
        // Output 1 when shift register shows stable pressed state (all 1s)
        w_debounced_signals[i] = &r_shift_regs[i];
    end
end
```

#### Output Registration
- Final output is registered to provide clean, glitch-free transitions
- Resets to all zeros on system reset

## Timing Characteristics

### Debounce Delay
- **Total delay** = `DEBOUNCE_DELAY` × `long_tick` period
- **Default**: 4 × 10ms = 40ms debounce time
- **Minimum stable time**: Button must remain stable for full delay period

### Response Time
- **Press detection**: `DEBOUNCE_DELAY` ticks after button stabilizes
- **Release detection**: `DEBOUNCE_DELAY` ticks after button releases
- **Asymmetric**: Same delay for both press and release

## Use Cases
- Mechanical pushbuttons and switches
- Rotary encoder inputs (with appropriate delay settings)
- Any digital input subject to contact bounce
- Both normally open and normally closed switch types

## Design Considerations
- **Delay tuning**: Adjust `DEBOUNCE_DELAY` based on switch characteristics
- **Tick frequency**: `long_tick` should be much slower than bounce duration
- **Multiple buttons**: All buttons share same debounce parameters
- **Reset behavior**: All outputs go low on reset, regardless of button states

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
