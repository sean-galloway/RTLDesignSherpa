---
title: Shifter IFSR Fibonacci
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

## Overview

The `shifter_lfsr_fibonacci` module implements a Fibonacci Linear Feedback Shift Register (LFSR) that is useful for generating pseudo-random binary sequences. This module is parameterizable, allowing for adjustments in width and the specific tap positions to be used in the feedback calculation.

## Parameters

- `WIDTH` (default: 8): Defines the width of the LFSR, specifying the number of bits in the shift register.
- `TAP_INDEX_WIDTH` (default: 12): Specifies the width for the index of each tap position, determining the maximum position index that can be used.
- `TAP_COUNT` (default: 4): Indicates the number of taps used to generate the feedback bit. These taps are XORed to produce the feedback.

## Inputs

- `i_clk`: Clock signal.
- `i_rst_n`: Active low reset signal.
- `i_enable`: Control signal to enable the LFSR shifting operation.
- `i_seed_load`: When high, load the seed value into the LFSR register.
- `i_seed_data [WIDTH-1:0]`: Seed value used to initialize the LFSR.
- `i_taps [TAP_COUNT*TAP_INDEX_WIDTH-1:0]`: Concatenated indices representing the tap positions within the LFSR.

## Outputs

- `o_lfsr_out [WIDTH-1:0]`: Output of the LFSR providing the current state of the shift register.
- `ow_lfsr_done`: Indicates when the LFSR has cycled through all its states and returned to the initial seed value.

## Functionality

- The Fibonacci LFSR shifts its internal state to the right at each clock cycle when enabled, inserting a feedback bit calculated as the XOR of selected bits determined by the `i_taps` input.
- The module allows for dynamic reconfiguration of the LFSR seed during operation through `i_seed_load` and `i_seed_data` signals.
- The feedback mechanism adheres to the Fibonacci LFSR configuration where the feedback bit is derived from XORing the bits at positions specified in the `i_taps` array.
- The `ow_lfsr_done` signal can be used to detect the completion of an LFSR cycle, indicating that the register has returned to its initial state.

## Usage

This module is suitable for applications requiring pseudo-random sequences, such as in cryptographic functions, pattern generation for test and verification, or any other domain needing a deterministic yet seemingly random sequence of data. The flexibility to configure the LFSR width and taps allows for customization to meet specific design requirements.

---

## Related Modules

- [Simple LFSR](shifter_lfsr)
- [Fibonacci LFSR](shifter_lfsr_fibonacci)
- [Galois LFSR](shifter_lfsr_galois)

---

[Return to Index](/docs/mark_down/rtl/)

---
