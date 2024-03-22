---
title: Math Adder Brent Kung sum
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `math_adder_brent_kung_sum` module calculates the summation part of a Brent-Kung adder. The Brent-Kung adder is a parallel prefix form adder, which offers a good compromise between speed and area, making it suitable for high-performance applications.

The module takes in two vectors, `i_p` for the propagate signal and `i_gg` for the generated signal, and calculates the bitwise sum and the carry-out value. The size of these vectors is determined by the parameter `N`.

## Parameter

- `N` (type `int`, default value `8`): The width of the input operands minus one. This defines the size of the vectors used in the operations.

## Ports

- `i_p [N:0]` (input, logic): Propagate signal vector. Its size is the value of the parameter `N` plus one.

- `i_gg [N:0]` (input, logic): Input carry generate signal vector. It is also the size of the parameter `N` plus one.

- `ow_sum [N-1:0]` (output, logic): Sum signal vector representing the addition result without the carry-out.

- `ow_carry` (output, logic): Carry-out signal from the addition operation.

## Sum Calculation

A generate loop with a `genvar k` is used to iterate over each input vector bit.

```verilog

genvar k;

generate

for (k = 0; k \< N; k = k + 1) begin : gen_loop

assign ow_sum[k] = i_gg[k] \^ i_p[k+1];

end

endgenerate

```

In each iteration of the loop, an element of the `ow_sum` output vector is calculated by performing an exclusive OR (`XOR`, represented by `\^`) operation between the corresponding elements of the `i_gg` and `i_p` vectors. The `i_p` vector is indexed with `k+1` because the propagation needs to consider the next significant bit.

### Usage

To use this module, instantiate it in your Verilog code and connect the input/output ports to the respective signals in your design. Ensure that the `N` parameter is set according to your requirements.

---

[Return to Index](/docs/mark_down/rtl/)

---
