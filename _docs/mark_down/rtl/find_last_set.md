---
title: Find Last Set
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This SystemVerilog module, `find_last_set`, is designed to find the last (most significant) bit set to 1 in a binary word and provide the index of that bit as its output.

## Parameters

- `WIDTH`: Specifies the size of the input data word; defaults to 32 bits.

- `INSTANCE_NAME`: A string parameter that can be used for instance identification during debugging, has no default value.

## Ports

- `i_data`: Input port carrying the data word of `WIDTH` bits for which the last set bit position needs to be found.

- `ow_index`: Output port containing the index (starting from 0) of the last bit set to 1.

## Functionality

The module uses the following internal parameters:

- `N`: A local parameter defined as `\$clog2(WIDTH) + 1`. It determines the number of bits required to represent the index.

It includes a function `find_last_set_index`, defined with an automatic storage class to avoid static linking and allow reentrant code. This function iterates over each bit in the input data, starting from the most significant bit, to find the index of the last set bit.

```verilog

function automatic [\$clog2(WIDTH):0] find_last_set_index;

input [WIDTH-1:0] input_data;

logic found;

begin

find_last_set_index = {\$clog2(WIDTH) + 1{1'b0}}; // Default value if no bit is set

found = 1'b0;

for (int i = WIDTH - 1; i >= 0 && !found; i--) begin

if (input_data[i]) begin

find_last_set_index = i;

found = 1'b1;

end

end

end

endfunction

```

### Operation

1\. The function initializes the index with all zeros, which will be the result if no bit is set in the input data.

2\. It sets a `found` flag to false to control loop termination once the last set bit has been found.

3\. A loop iterating from the MSB to LSB of the input data checks each bit.

4\. The function returns its index if a set bit is found.

5\. The loop stops on the first set bit located (due to the `!found` condition).

The main combinatorial block in the module uses this function to continuously update the `ow_index` output port with the index of the last set bit in the `i_data` input.

A commented-out `\$display` statement illustrates how one might use the `INSTANCE_NAME` parameter to print debugging information about the module instance, the data being processed, and the simulation time when a set bit is found.

---

[Return to Index](/docs/mark_down/rtl/)

---
