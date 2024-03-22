---
title: Utiles
layout: docs
date: 2024-01-02
categories: ["script"]
---

The `utils` module is located at `rtl_generators/utils/utils.py` and includes several essential functions and classes related to generating Verilog code for various hardware components. This module notably imports several classes that correspond to components of parallel prefix adders such as Brent-Kung adders (PG, BitwisePGLogic, GroupPGLogic, SumLogic, BrentKungAdder, Black, Gray) and also multipliers like Dadda and Wallace tree multipliers (DaddaTree, WallaceTree).

## Function `write_module(file_path, module)`

This function outputs a module into a SystemVerilog file. The module’s SystemVerilog representation is created by calling its `verilog` method, generating the code, and writing it into a file at `file_path`.

### Parameters

- `file_path`: The save file path for the SystemVerilog code.

- `module`: An instance of the module for writing to a file. This module should have a `module_name` attribute for the file name and a `verilog` method for code generation.

### Behavior

The function formats the filename using the `module_name` and generates the SystemVerilog code by calling the `module.verilog` method, and notifies the user about the generation by printing the name of the generated module.

## Function `write_dadda(file_path, buswidth)`

This function facilitates the generation of a DaddaTree multiplier with the specified bus width. It prints "Generated:" to the console, indicating that the generation process is starting, and then uses `write_module` to generate the code and write it to a file.

### Parameters, write_dadda

- `file_path`: The DaddaTree Multiplier file path.

- `buswidth`: The bus width for the Dadda multiplier.

## Function `write_wallace(file_path, type, buswidth)`

This function generates a WallaceTree multiplier and carries out steps similar to `write_dadda`.

### Parameters, write_wallace

- `file_path`: The WallaceTree Multiplier file path.

- `type`: The WallaceTree multiplier type. It affects the instantiation of the `WallaceTree` class.

- `buswidth`: The bus width for the Wallace multiplier.

## Function `write_bk(file_path, buswidth)`

This function generates a Brent-Kung adder and its associated components. It creates instances of classes such as Black, Gray, PG, BitwisePGLogic, GroupPGLogic, SumLogic, and BrentKungAdder and writes each generated SystemVerilog module using `write_module`.

### Parameters, write_bk

- `file_path`: The Brent-Kung file path.

- `buswidth`: The Brent-Kung bus width.

These functions are critical in automated hardware design systems for generating complex modules like multipliers and adders programmatically based on design parameters like bus width.

---

## Block Hierarchy and Links

- [Module Class](module)
- [Parser Helper Class](verilog_parser)
- [Signal Class](signal)
- [Parameter Class](param)
- [Utils](utils)

---

[Back to Scripts Index](index)

---
