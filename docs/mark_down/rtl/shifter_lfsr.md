# shifter_lfsr

This Verilog module implements a parameterizable Linear Feedback Shift Register (LFSR). An LFSR generates pseudo-random bit sequences, commonly applied in cryptography, error detection/correction, and digital signal processing. Please refer to the documentation in reference/lfsr_table.pdf for how to configure this LFSR.

## Parameters

- `N`: Defines the width of the LFSR. The default value is 5 bits.

## Inputs

- `i_clk` (wire): System clock input.

- `i_rst_n` (wire): Active low reset signal.

- `i_enable` (wire): Enable signal for LFSR operation.

- `i_seed_load` (wire): When high, the module will load the `i_seed_data` into the shift register.

- `i_seed_data` (wire[N-1:0]): Seed data loaded into the LFSR when `i_seed_load` is set high.

- `i_taps` (wire[N-1:0]): Specifies the tap positions used for the feedback function. XOR/XNOR function should be applied on the selected taps.

## Outputs

- `o_lfsr_data` (reg[N-1:0]): Current content of the LFSR.

- `ow_lfsr_done` (reg): Signal to indicate the LFSR has cycled through all its states and returned to the initial seed value.

## Internal Signals

- `r_lfsr_reg` (reg[N-1:0]): The internal shift register that holds the current LFSR value.

- `r_xnor_out` (reg): The result of applying an XNOR operation on the tapped bits and the LFSR value.

## Functionality

- **Reset Operation**: On a falling edge of `i_rst_n`, the internal LFSR state `r_lfsr_reg` and the output `r_xnor_out` are reset to zero.

- **Shifting Operation**: On each rising edge of the clock `i_clk`, if the enable input `i_enable` is set, the module either loads `i_seed_data` into `r_lfsr_reg` (`i_seed_load` high) or shifts the register left by one, pushing in the value of `r_xnor_out` at the LSB position.

- **Feedback Calculation**: An XNOR-based feedback is calculated using the current LFSR state and the specified tap positions. The result is stored in `r_xnor_out`.

- **Done Condition**: The output `ow_lfsr_done` is set high when the content of `r_lfsr_reg`, excluding the LSB, matches the `i_seed_data`, indicating that the LFSR has completed a full cycle and returned to its initial state.

## Notes

- It is essential to provide proper tap positions to create a maximum-length LFSR, which will cycle through all possible states (except the all-zero state) before repeating.

- The attached PDF (not provided here) should be consulted for choosing the correct taps for a given LFSR width to ensure the desired sequence properties.

---

[Return to Index](index.md)

----------
