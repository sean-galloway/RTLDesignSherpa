---
title: Encoder Priority Enable
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `encoder_priority_enable` module is a Verilog construct designed for priority encoding a binary input based on its width. The module's functionality is governed by parameterization and controlled by an enable signal.

## Parameters

- `WIDTH`: the size of the input vector defaults to 8 bits.

## Ports

- `i_priority` (Input): A logic vector of width `WIDTH`, representing the signals to be priority encoded.

- `i_enable` (Input): A single-bit logic signal that turns the encoding on or off.

- `ow_encode` (Output): A logic vector resulting from priority encoding `i_priority`. Its width is determined by `\$clog2(WIDTH)`, which calculates the number of bits needed to represent the highest index of a binary vector of length `WIDTH`.

## Functionality

The module performs priority encoding on the `i_priority` input when `i_enable` is asserted. Priority encoding converts a binary vector into an index of the highest priority '1' bit. If `i_enable` is de-asserted, encoding is disabled, and the `ow_encode` output is zero.

## Internal Workings

1\. A `logic` flag `found` indicates whether at least one '1' has been found during encoding.

2\. The `always_comb` block indicates combinatorial logic that evaluates every time an input changes.

3\. If `i_enable` is '0', priority encoding is bypassed: `ow_encode` is explicitly set to a vector of zeroes.

4\. Otherwise, a temporary variable `w_priority_levels` stores which levels are active (`'1'`).

5\. A for-loop iterates over all levels of `i_priority`. If a level is active, it sets the corresponding bit in `w_priority_levels` and marks `found` as '1'.

6\. After the loop, if `found` is '1', `ow_encode` is set to the result of `\$onehot(w_priority_levels)` which performs the priority encoding. If `found` is '0', indicating no bits were set, `ow_encode` is again zeroed out.

### Notes

- The `\$onehot` operator is used to one-hot encode the highest priority '1' found in `w_priority_levels`.

- The module uses parameterized width, allowing for flexibility in the size of the input signals.

---

[Return to Index](/docs/mark_down/rtl/)

---
