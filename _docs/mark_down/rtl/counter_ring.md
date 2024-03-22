---
title: Counter Ring
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The ring counter is a simple, cyclic counter that iterates through a series of binary states, with a single high bit cycling through from the most significant bit (MSB) to the least significant bit (LSB) and then wrapping around. It is a useful construct in digital logic for situations where a sequence of activations is needed, such as controlling a multiplexed display or generating timing sequences.

## Module: `counter_ring`

### Parameters

- `WIDTH`: The width of the ring counter in bits. This parameter determines the number of unique states the counter will cycle through.

### Ports

- `i_clk` (input, wire): The system clock signal. The counter advances on the rising edge of this clock.
- `i_rst_n` (input, wire): An active-low reset signal. When this signal is low, the counter is reset to its initial state.
- `i_enable` (input, wire): A signal to enable the counter. When high, the counter advances its state on each clock cycle.
- `o_ring_out` (output, reg): The current value of the ring counter. This output will have exactly one high bit, which rotates through each bit position in the counter.

### Functionality

At reset (`i_rst_n` is low), the ring counter initializes to a state where the least significant bit is set high (e.g., `0001` for a 4-bit counter). When enabled (`i_enable` is high), the ring counter advances its state on each rising edge of the clock:

1. The single high bit rotates right through the counter's bit positions.
2. When the high bit reaches the LSB, it wraps around the MSB in the next cycle.

For example, in a 4-bit ring counter, the sequence of states would be `0001`, `1000`, `0100`, `0010`, and then back to `0001`.

---

[Return to Index](/docs/mark_down/rtl/)

---
