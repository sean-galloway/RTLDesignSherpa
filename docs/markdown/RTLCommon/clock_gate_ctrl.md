# clock_gate_ctrl

This SystemVerilog module implements an intelligent clock gating controller that manages power consumption by controlling when a clock is gated based on idle time.

## Module Parameters

- `IDLE_CNTR_WIDTH`: An integer parameter with a default value of 4 that sets the width of the idle counter.
- `N`: An integer parameter that defaults to `IDLE_CNTR_WIDTH`, providing an alias for the counter width.

## Ports

Inputs:

- `clk_in`: The input clock signal to be gated.
- `aresetn`: Active-low asynchronous reset signal.
- `i_cfg_cg_enable`: Global clock gating enable control.
- `i_cfg_cg_idle_count`: An N-bit input that configures the idle count threshold before gating.
- `i_wakeup`: Signal to wake up the block and prevent clock gating.

Outputs:

- `clk_out`: The gated clock output.
- `o_gating`: Status signal indicating when clock gating is active.

## Functionality

1. **Idle Counter Management**:
   - The module maintains an N-bit counter (`r_idle_counter`) that counts down from the configured idle count value.
   - Upon reset, the counter is initialized with the value from `i_cfg_cg_idle_count`.
   - When `i_wakeup` is asserted or clock gating is globally disabled, the counter resets to the configured idle count.
   - During normal operation, the counter decrements until it reaches zero, at which point it remains at zero.

2. **Gating Control Logic**:
   - Clock gating is enabled when three conditions are met:
     - The global clock gating enable (`i_cfg_cg_enable`) is active.
     - The wakeup signal (`i_wakeup`) is inactive.
     - The idle counter has reached zero.

3. **Clock Gating Implementation**:
   - The module instantiates an `icg` (Integrated Clock Gating) cell to perform the actual clock gating.
   - The enable signal to the ICG is the inverse of the gating condition, as the ICG expects an active-high enable.

4. **Status Output**:
   - The `o_gating` output reflects the current gating state, which is useful for monitoring or debugging.

## Implementation Notes

- The module provides a flexible way to control clock gating based on idle time, which is useful for power optimization.
- The configurable idle count allows for tuning the aggressiveness of power saving based on system requirements.
- The wakeup signal provides a mechanism for external logic to override clock gating when activity is imminent.

## Usage Considerations

- The idle count should be set based on the expected activation patterns of the downstream logic.
- A smaller idle count results in more aggressive power saving but may lead to more frequent clock re-enabling.
- The wakeup signal should be asserted early enough to ensure the clock is available when needed.

---

[Return to Index](index.md)

---