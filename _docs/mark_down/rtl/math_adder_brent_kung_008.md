---
title: Math Adder Brent Kung 008
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This module implements an `N`-bit Brent-Kung adder. The Brent-Kung adder is a parallel prefix form of the carry-lookahead adder, which offers a good trade-off between gate depth (latency) and the number of operations (area). It is commonly used in applications where low latency is critical.

## Parameters

- `N`: The width of the operands; defines the bit-size of numbers to add.

## Ports

- `i_a [N-1:0]`: Bit-vector for the first operand (addend).

- `i_b [N-1:0]`: Bit-vector for the second operand (addend).

- `i_c`: Single bit input for the initial carry (typically 0 for addition).

- `ow_sum [N-1:0]`: Bit-vector for the sum output.

- `ow_carry`: Single-bit output for the carry-out of the addition.

## Internal Signals

- `ow_g [N:0]`: Carry generates an intermediate signal.

- `ow_p [N:0]`: Carry propagate an intermediate signal.

- `ow_gg [N:0]`: Group generates an intermediate signal used for carrying computation.

## Sub-modules

- `math_adder_brent_kung_bitwisepg`: Compute bitwise generate and propagate signals.

- `math_adder_brent_kung_grouppg_008`: Compute group generates signals for carrying.

- `math_adder_brent_kung_sum`: Compute the final sum and carry based on propagate and group generate signals.

## Simulation-specific Constructs

- The `\$dumpfile` and `\$dumpvars` system calls are used for waveform dumping during simulation, which is not synthesized to actual hardware and is enclosed within synthesis-off directives `// synopsys translate_off` and `// synopsys translate_on`.

## Usage Notes

- To instantiate this module, you must provide a parameter `N`, the operation width, specify the input operands `i_a` and `i_b`, and, if needed, initialize the carry input `i_c`. Then connect the `ow_sum` and `ow_carry` to receive the result of the addition.

### Files and Modules Dependencies

To properly use this module, make sure that the following files/modules are included in your project:

- `math_adder_brent_kung_bitwisepg.sv`

- `math_adder_brent_kung_grouppg_008.sv`

- `math_adder_brent_kung_sum.sv`

---

[Return to Index](/docs/mark_down/rtl/)

---
