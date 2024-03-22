---
title: Math Adder Hierarchical
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This SystemVerilog module implements a hierarchical adder structure to sum an array of numbers using Carry Lookahead Adders (CLA). This structure facilitates the addition of multiple numbers concurrently, significantly reducing the overall add time compared to a linear chain of adders.

## Parameters

- **N**: Bit-width of the individual numbers to be summed.

- **C**: The number of numbers to be summed.

## Ports

- **i_numbers [0:C-1]**: Input array of numbers, each N bits wide.

- **ow_sum**: Output sum, N bits wide.

## Functionality

1\. **Initialization**: The input array `i_numbers` is padded to a length of a power of two, ensuring complete binary tree construction in later stages. This padding is initialized to zeros.

2\. **Hierarchical Addition**: The hierarchical adder is created using a generate block, which successively stages partial sums using Carry Lookahead Adders. The stages reduce the number of addends by half each time, eventually leading to a single sum output.

3\. **Final Output Assignment**: The final output `ow_sum` is the first (and only) element of the last stage's intermediate sums.

## Hierarchical Structure

- The module uses a generated structure to create multiple stages (`Stages`) where each stage has half the number of operations as the previous one.

- The intermediate sums and carries are stored in 2D arrays with indices indicating stage and position within the stage.

- In each stage, pairs of numbers are added using instances of a `math_adder_carry_lookahead`.

## Debug Features

When `DEBUG` is defined:

- **Flattened Input Numbers and Intermediate Sums**: Input numbers and intermediate results are flattened into one-dimensional arrays for easy monitoring in debug tools.

- **Carry Signal Flattening**: The carry signals throughout the addition process are flattened.

- **VCD Dumping**: Waveform data dumping is enabled for simulation purposes, writing to a file named `waves.vcd`.

---

[Return to Index](/docs/mark_down/rtl/)

---
