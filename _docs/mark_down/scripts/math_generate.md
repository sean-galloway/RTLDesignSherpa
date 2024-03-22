---
title: Math Generate
layout: docs
date: 2024-01-02
categories: ["script"]
---

This script is a command-line Python program located at `math_generate.py`. It generates RTL modules for different adders and multipliers with a specified bitwidth.

## Command Line Options

- `--path`: The output file path.

- `--type`: Determines the type of the adder to generate. Valid types are `brent_kung`, `dadda`, `wallace_fa`, and `wallace_csa`.

- `--buswidth`: Defines the bit width for the adder. The width must be a power of 2.

## Functionality

- `get_args()`: Parses and returns the command line arguments provided by the user.

- `_main(args)`: Validates the adder type and bus width. Calls the corresponding function to write out the RTL based on the adder type using imported functions `write_bk()`, `write_dadda()`, and `write_wallace()` from the `rtl_generators.utils` module.

## Internal Details

- The program asserts that the `--type` option must be within the valid adder types listed in `valid_types`.

- It also asserts that the `--buswidth` must be a power of 2 by checking if the logarithm base 2 of `buswidth` is an integer.

- Depending on the `type` specified, the relevant method (`write_bk`, `write_dadda`, or `write_wallace`) is called with the `path` and `buswidth` as arguments.

## Example Command

The math_generate.sh file lists all of the command line options. Here is one of them:

```bash

out_path='./math_outputs/bk_08'

if [ ! -d "\$out_path" ]; then

mkdir -p "\$out_path"

echo "Directory '\$out_path' created."

else

echo "Directory '\$out_path' already exists."

fi

rm -f $out_path/*

# Adder Type

type='brent_kung'

# Bitwidth

buswidth=8

math_generate.py --type $type --path $out_path --buswidth $buswidth

```

---

[Back to Scripts Index](index)

---
