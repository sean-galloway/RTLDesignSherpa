---
title: Decoder
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The Verilog code defines a parameterized decoder module.

## Parameters

- **M**: An integer parameter specifies the number of input bits. Its default value is 4.

- **N**: It is an integer parameter given by `2 ** M`, representing the number of output bits. For the default M value of 4, N would be 16.

## Ports

- **i_encoded**: An input bus of size [M-1:0] carrying the encoded signal (binary number) to be decoded.

- **o_data**: An output bus of size [N-1:0] carrying the decoded output as a one-hot code.

## Functionality

The decoder initializes all output bits `o_data` to zero. Then, it enters a `generate` block, which uses a `for` loop to iterate N times, creating a separate connection for each bit of the `o_data` bus.

Each iteration `i` checks if the input bus `i_encoded` matches the current iteration index (`i`). If there is a match, it assigns the corresponding bit in `o_data` as high (logic 1). Otherwise, the bit remains low (logic 0). This effectively converts a binary encoded input to a one-hot encoded output.

### Example

If `M` is 3, there would be an 8-bit output since `N` would be `2³ = 8`. For `i_encoded` equal to 3 (`011` in binary), `o_data` would be `00001000`.

### Usage

The module can be instantiated in a larger design, setting the desired `M` (and implicitly `N`) parameters if the defaults are unsuitable.

```verilog

decoder #(.M(3)) my_decoder (

.i_encoded(some_encoded_input),

.o_data(decoded_output)

);

```

This example would instantiate a decoder with three input bits and eight output bits, connected to signals `some_encoded_input` and `decoded_output`, respectively.

---

[Return to Index](/docs/mark_down/rtl/)

---
