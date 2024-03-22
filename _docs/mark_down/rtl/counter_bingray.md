---
title: Counter Bin Gray
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `counter_bingray` module is a parameterized gray counter, implemented as a SystemVerilog module, typically used to synchronize asynchronous clock domains, such as in FIFO (First In, First Out) buffers. It features a binary counter translated into Gray code, as Gray code only has one bit change between successive values, making it more error-proof for specific applications.

## Parameters

- `WIDTH`: The bit-width of the counter, defaulting to 4. This parameter can be modified to suit the desired counter width.

## Inputs

- `i_clk`: The clock signal for the counter.

- `i_rst_n`: An active-low asynchronous reset signal.

- `i_enable`: A logic signal to turn the counter incrementation on or off.

## Outputs

- `o_counter_bin`: The current value of the binary counter.

- `o_counter_gray`: The Gray code representation of the binary counter.

## Internal Signals

- `w_counter_bin`: A wire representing the next value of the binary counter.

- `w_counter_gray`: A wire representing the Gray code equivalent of `w_counter_bin`.

## Functionality

- Upon the rising edge of the clock (`i_clk`) or the falling edge of the reset (`i_rst_n`):

- If the reset is asserted (active low), the binary and Gray counter outputs are cleared to 0.

- The binary counter is incremented if the reset is not asserted and the enable signal (`i_enable`) is high. The Gray code output is updated based on the new binary counter value.

## Usage

To use this module, instantiate it in your Verilog design and connect the appropriate signals. Adjust the `WIDTH` parameter to match the desired counter size for your design's requirements if necessary.

For the counters to operate correctly, ensure a proper clock signal is provided and assert and de-assert the reset appropriately. The enable signal should be controlled based on whether the counter needs to run or halt.

For further integration into larger designs like asynchronous FIFOs, use the Gray code output to pass counter states across clock domains safely.

---

[Return to Index](/docs/mark_down/rtl/)

---
