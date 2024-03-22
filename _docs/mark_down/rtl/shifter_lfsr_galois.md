---
title: Shifter IFSR galois
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

## Overview

The `shifter_lfsr_galois` module implements a Galois Linear Feedback Shift Register (LFSR), an efficient structure for generating pseudo-random binary sequences with reduced logic and feedback path complexity. This module offers parameterization for the LFSR width and the tap configuration.

## Parameters

- `WIDTH` (default: 8): Defines the number of bits in the LFSR, indicating the register size.
- `TAP_INDEX_WIDTH` (default: 12): Specifies the width for the index of each tap position, enabling a wide range of tap positions.
- `TAP_COUNT` (default: 4): Determines the number of taps that influence the feedback bit calculation.

## Inputs

- `i_clk`: Clock input.
- `i_rst_n`: Active low asynchronous reset.
- `i_enable`: LFSR operation enables signal.
- `i_seed_load`: When asserted, loads the `i_seed_data` into the LFSR.
- `i_seed_data [WIDTH-1:0]`: Seed value for initializing or resetting the LFSR.
- `i_taps [TAP_COUNT*TAP_INDEX_WIDTH-1:0]`: Encoded tap positions used for LFSR feedback calculation.

## Outputs

- `o_lfsr_out [WIDTH-1:0]`: The current state of the LFSR, outputting the pseudo-random sequence.
- `ow_lfsr_done`: Signal that indicates the LFSR has completed a full cycle and returned to the initial seed state.

## Functionality

- The Galois LFSR configuration allows for feedback directly into specific tap positions, reducing the number of gates compared to the traditional Fibonacci LFSR.
- On each clock cycle where `i_enable` is high, the LFSR state is updated based on the Galois method: bits are shifted right, and conditional XOR operations are performed based on the feedback from the most significant bit.
- The `i_seed_load` input facilitates dynamic reseeding of the LFSR, offering flexibility for various use cases.
- The `ow_lfsr_done` output can be utilized to monitor the completion of sequence cycles, particularly useful in scenarios requiring deterministic random behavior across fixed intervals.

## Usage

The Galois LFSR in this configuration is suited for applications needing efficient pseudo-random sequence generation, such as scrambling, noise generation, or Monte Carlo simulations. Its parameterizability enhances adaptability, allowing designers to tailor the LFSR to specific requirements regarding sequence length and complexity.

---

## Related Modules

- [Simple LFSR](shifter_lfsr)
- [Fibonacci LFSR](shifter_lfsr_fibonacci)
- [Galois LFSR](shifter_lfsr_galois)

---

[Return to Index](/docs/mark_down/rtl/)

---
