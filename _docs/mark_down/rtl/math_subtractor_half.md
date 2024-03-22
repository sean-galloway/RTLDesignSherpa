---
title: Math Subtractor half
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

A half subtractor is a digital circuit that subtracts two binary digits. It has two inputs and two outputs. The inputs are typically labeled as i_a (minuend) and i_b (subtrahend), and the outputs are Difference (o_d) and Borrow (o_b).

## Inputs

- `i_a`: The first single-bit binary input to the subtractor. It represents the minuend in the subtraction operation.

- `i_b`: The second single-bit binary input to the subtractor. It represents the subtrahend in the subtraction operation.

## Outputs

- `o_d`: The single-bit binary output representing the difference resulting from the subtraction of `i_b` from `i_a`.

- `o_b`: The single-bit binary output representing the borrow bit. If `i_b` exceeds `i_a`, `o_b` will be set to `1`, indicating a borrow.

## Functionality

- The `o_d` (difference) output is determined by the bitwise exclusive OR (XOR) of the inputs `i_a` and `i_b`.

- The `o_b` (borrow) output is determined by the bitwise AND of the negated `i_a` and `i_b`. This means that the borrow bit is asserted (`o_b` = 1) only when `i_a` is 0 and `i_b` is 1.

## Usage

This module does not have parameters or settings and can be instantiated as-is. You would typically include it in a larger module to use in your design. For example:

## Notes

- The half subtractor performs the subtraction of two single-bit numbers.

- Since no `include` or `import` statement precedes the module declaration, this module doesn't depend on external definitions or packages.

---

[Return to Index](/docs/mark_down/rtl/)

---
