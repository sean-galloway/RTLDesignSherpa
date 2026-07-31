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
Kills mechanical switch bounce by sampling button inputs on a regular tick and refusing to believe a button until the same state shows up for several consecutive samples.

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
- **`PRESSED_STATE`** - Logic level when button is pressed (default: 1; 1 for normally open, 0 for normally closed)

## Implementation Details

### Core Algorithm
The module tracks each button's recent history in a shift register:

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
- Only samples inputs when `long_tick` fires
- Over-sampling invites false triggering—this avoids it
- Typical `long_tick` period: ~10ms

#### Button Type Support
- **Normally Open (NO)**: `PRESSED_STATE = 1`
  - Button reads '0' when not pressed, '1' when pressed
- **Normally Closed (NC)**: `PRESSED_STATE = 0`  
  - Button reads '1' when not pressed, '0' when pressed
- The input inversion handles NC buttons transparently

#### Debounce Logic
- Keeps `DEBOUNCE_DELAY` samples per button
- The output only goes high when every sample in the shift register is '1'
- Which means the button has to sit stable in the pressed state for the whole delay

```systemverilog
always_comb begin
    for (int i = 0; i < N; i++) begin
        // Output 1 when shift register shows stable pressed state (all 1s)
        w_debounced_signals[i] = &r_shift_regs[i];
    end
end
```

#### Output Registration
- The final output is registered, so transitions come out clean and glitch-free
- Resets to all zeros on system reset

## Timing Characteristics

### Debounce Delay
- **Total delay** = `DEBOUNCE_DELAY` × `long_tick` period
- **Default**: 4 × 10ms = 40ms debounce time
- **Minimum stable time**: The button has to hold steady for the full delay period

### Response Time
- **Press detection**: `DEBOUNCE_DELAY` ticks after the button stabilizes high
  (the output is `&r_shift_regs[i]`, so it needs `DEBOUNCE_DELAY` consecutive
  high samples to assert)
- **Release detection**: ~1 tick (+1 clk). The output is an AND-reduce, so the
  first `0` shifted in on release immediately clears it — release is **not**
  debounced beyond a single sample.
- **Asymmetric**: press is fully debounced; release propagates ~`DEBOUNCE_DELAY`×
  faster. Do NOT rely on symmetric debounce timing.

## Use Cases
- Mechanical pushbuttons and switches
- Rotary encoder inputs (with the delay set appropriately)
- Any digital input prone to contact bounce
- Both normally open and normally closed switch types

## Design Considerations
- **Delay tuning**: Set `DEBOUNCE_DELAY` to match your switch's characteristics
- **Tick frequency**: `long_tick` should run much slower than the bounce duration
- **Multiple buttons**: All buttons share the same debounce parameters
- **Reset behavior**: All outputs go low on reset, no matter what the buttons are doing

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
