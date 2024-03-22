---
title: Math Subtractor full
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

A full subtractor is a digital circuit that computes the difference of three bits: two input bits and a borrow-in bit. It outputs the difference and borrow-out bit, used for subtraction in binary systems.

## Inputs/Outputs and Internal Functionality

- **Inputs:**

- `i_a`: This single-bit logic signal represents the subtraction operation's minuend.

- `i_b`: A single-bit logic signal that represents the subtrahend.

- `i_b_in`: Also a single-bit logic signal known as the "borrow in". This input cascades several `math_subtractor_full` modules to perform multi-bit subtractions.

- **Outputs:**

- `ow_d`: Represents the "difference" output. It's a single-bit logic signal resulting from the subtracting operation applied to `i_a`, `i_b`, and `i_b_in`.

- `ow_b`: The "borrow out" output. It's a single-bit logic signal indicating whether a borrow has occurred during the subtraction.

## Detailed Explanation

The operation performed by the module `math_subtractor_full` is a full subtractor. A full subtractor considers three bits: the two bits being subtracted and the borrowed bit from the previous stage in a multi-bit subtraction operation.

- The difference output `ow_d` is computed by xor-ing the inputs `i_a`, `i_b`, and `i_b_in`. This reflects the basic operation of a binary full subtractor where the difference bit is the xor of all inputs.

- The Boolean operation determines the borrow output `ow_b`. Two terms compute it:

- `(~i_a & i_b)` signifies that borrow is needed if we have a '0' from `i_a` and a '1' from `i_b`.

- `(~(i_a \^ i_b) & i_b_in)` indicates that if `i_a` and `i_b` are equal (both 0 or both 1) and the borrow in `i_b_in` is 1 (indicating that a borrow was needed from the previous stage), then a borrow is propagated to the next stage.

This block requires No command line options, as it is a synthesizable hardware description, and the input signals fully define the module's behavior.

This module is typically instantiated inside a larger design and connected to other components. Multiple instances of the `math_subtractor_full` blocks can be cascaded together to form a subtractor for larger bit-widths, making sure to correctly connect the borrow out (`ow_b`) of one stage to the borrow in (`i_b_in`) of the next stage.

---

[Return to Index](/docs/mark_down/rtl/)

---
