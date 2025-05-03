# counter_freq_invariant

This SystemVerilog module implements a configurable frequency divider with a counter output. It allows for selecting different division factors to produce a counter that increments at different frequencies.

## Module Parameters

- `COUNTER_WIDTH`: An integer parameter (default: 5) that defines the width of the output counter.

## Ports

Inputs:

- `i_clk`: The input clock signal.
- `i_rst_n`: Active-low reset signal.
- `i_freq_sel`: A 4-bit input that selects the frequency division factor.

Outputs:

- `o_counter`: A counter output with width defined by the `COUNTER_WIDTH` parameter.
- `o_tick`: A pulse signal that is asserted for one cycle each time the counter reaches its maximum value.

## Functionality

1. **Frequency Selection**:
   - The module supports 16 different frequency division options (0-15).
   - Division factors range from 1:1 (1GHz) to 10000:1 (100kHz), assuming a 1GHz input clock.
   - A combinational lookup table maps the `i_freq_sel` value to the appropriate division factor.

2. **Frequency Change Detection**:
   - The module detects changes in the frequency selection input.
   - When the frequency selection changes, a one-cycle clear pulse is generated.

3. **Prescaler Counter**:
   - Uses the `counter_load_clear` module to implement the frequency division.
   - The prescaler counts up to the selected division factor and generates a done signal.
   - When the frequency selection changes, the prescaler is cleared and restarted.

4. **Output Counter and Tick Generation**:
   - The `o_counter` increments on each prescaler done signal.
   - It naturally rolls over at 2^COUNTER_WIDTH.
   - The `o_tick` signal is asserted for one cycle when the prescaler completes and the counter is at its maximum value.
   - The counter is cleared when the frequency selection changes.

## Implementation Notes

- The division factors are selected to provide common frequencies when dividing a 1GHz clock.
- The prescaler counter uses a 32-bit parameter for its maximum value instead of 16-bit.
- The module is designed to smoothly handle frequency selection changes by resetting internal counters.

---

[Return to Index](index.md)

---