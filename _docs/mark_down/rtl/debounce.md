---
title: Debounce
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `debounce` module removes the mechanical noise commonly associated with button presses, which can cause multiple transitions on a digital input when only a single button press is intended. The debouncing is achieved through a shift-register-like approach, incorporating a delay that filters out bounces. Assertion and de-assertion debouncing are handled.

## Description

The debounce module stabilizes the input signals from mechanical buttons or switches. It filters out the noise and glitches typically associated with mechanical switch toggling, ensuring a clean and stable digital signal as output.

## Parameters

- `N`: Number of buttons (input signals). The default is 4.
- `DEBOUNCE_DELAY`: Debounce delay in clock cycles. The default is 4.
- `PRESSED_STATE`: Determines the expected active state of the button when pressed. Set to 1 for normally open (NO) buttons, where the button signal is high when pressed. Set to 0 for normally closed (NC) buttons, where the button signal is low when pressed. The default is 1.

## Inputs

- `i_clk`: Clock signal. Synchronizes the operation of the debounce logic.
- `i_rst_n`: Active low reset signal. Resets the module's internal states when low.
- `i_long_tick`: A periodic signal (~10ms tick) used to sample the button states. Ensures that the button states sampling occurs at regular, long-duration intervals.
- `i_button [N-1:0]`: Array of input button signals for debouncing. Each element corresponds to a button.

## Outputs

- `o_button [N-1:0]`: Array of debounced output signals. Each element corresponds to the debounced state of the respective input button.

## Functionality

- On every positive edge of the clock (`i_clk`) or when the reset (`i_rst_n`) goes low:
  - If reset is low, all internal shift registers get cleared to 0.
  - Otherwise, if the `i_long_tick` signal is high, the current state of each button is pushed into its corresponding shift register, inverting the signal if `PRESSED_STATE` is 0.
- The module checks if the contents of each shift register represent a stable state (either all 1s or all 0s) using a combination of bitwise AND (`&`) and NOR (`~|`) operations.
- The stable state (if detected) is then passed to the output, providing a clean, debounced signal for each button.

### Additional Notes

- The `debounce` module uses SystemVerilog constructs such as parameterized modules and arrayed instances of storage elements, which provide flexibility in specifying the number of signals to debounce and the depth of the debouncing delay.

- This module handles assertion and de-assertion debouncing by default.

---

[Return to Index](/docs/mark_down/rtl/)

---
