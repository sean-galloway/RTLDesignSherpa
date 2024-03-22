---
title: Shifter Barrel
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `shifter_barrel` module is a hardware component written in SystemVerilog that performs various shift operations on an input data signal. A control signal determines the type of shift operation. It allows for wrapped and non-wrapped right and left and arithmetic right shifts. This is commonly used in an ALU circuit.

## Parameters

- `WIDTH`: A positive integer that sets the bit-width of the input and output data signals.

## Ports

- `i_data` (input): The data signal to be shifted, with a width defined by the `WIDTH` parameter.

- `i_ctrl` (input): A 3-bit control signal determining the type of shift operation to perform.

- `i_shift_amount` (input): The number of positions to shift, which can range from 0 to the bit-width of the data.

- `ow_data_out` (output): The result of the shift operation, with the same width as the `i_data` input.

## Internal Functionality

- The module supports shift operations based on the `i_ctrl` value provided.

| `i_ctrl` Value | Operation | Description |

| ------- | ----------------------------- | --------------------------------------------------------- |

| 000 | No Shift | Output data equals input data (no shift). |

| 001 | Logical Right Shift (no wrap) | Right shifts the input data bits without wrapping. |

| 010 | Arithmetic Right Shift | Right shifts the bits while preserving the sign bit. |

| 011 | Logical Right Shift (wrap) | Right shifts with wrapping around to the left side. |

| 100 | Logical Left Shift (no wrap) | Left shifts the bits without wrapping or sign extension. |

| 110 | Logical Left Shift (wrap) | Left shifts with wrapping around to the right side. |

- The `shift_amount_mod` uses the modulo operation to ensure the shift amount is within the range of the data width.

- Two local arrays, `w_array_rs` and `w_array_ls`, compute possible shifted values for both directions. They are unrolled in for-loops for synthesizable hardware looping.

- The final shifted value is selected based on the value of `i_ctrl` using a combinatorial always block.

---

[Return to Index](/docs/mark_down/rtl/)

---
