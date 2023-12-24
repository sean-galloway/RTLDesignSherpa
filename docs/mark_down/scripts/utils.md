# utils

The `utils` module is located at `rtl_generators/utils/utils.py` and includes several important functions and classes that relate to the generation of Verilog code for various hardware components. This module notably imports several classes that correspond to components of parallel prefix adders such as Brent-Kung adders (PG, BitwisePGLogic, GroupPGLogic, SumLogic, BrentKungAdder, Black, Gray) and also multipliers like Dadda and Wallace tree multipliers (DaddaTree, WallaceTree).

## Function `write_module(file_path, module)`

This function is used to output a module into a SystemVerilog file. The module’s SystemVerilog representation is created by calling its `verilog` method, which presumably generates the code and writes it into a file located at `file_path`.

### Parameters

- `file_path`: The file path where the SystemVerilog code will be saved.
- `module`: An instance of the module to be written to the file. This module should have a `module_name` attribute used for the file name, and a `verilog` method for code generation.

### Behavior

The function formats the filename using the `module_name`, generates the SystemVerilog code by calling the `module.verilog` method, and notifies the user about the generation by printing the name of the generated module.

## Function `write_dadda(file_path, buswidth)`

This function facilitates the generation of a DaddaTree multiplier with the specified bus width. It prints "Generated:" to the console, indicating that the generation process is starting, and then uses `write_module` to generate the code and write it to a file.

### Parameters, write_dadda

- `file_path`: The directory path where the SystemVerilog file for the DaddaTree multiplier should be saved.
- `buswidth`: The width of the buses for which the Dadda multiplier is generated.

## Function `write_wallace(file_path, type, buswidth)`

This function is responsible for generating a WallaceTree multiplier and carries out steps similar to `write_dadda`.

### Parameters, write_wallace

- `file_path`: The directory path where the SystemVerilog file for the WallaceTree multiplier should be saved.
- `type`: The type of WallaceTree multiplier being generated. It affects the instantiation of the `WallaceTree` class.
- `buswidth`: The bus width for which the Wallace multiplier is generated.

## Function `write_bk(file_path, buswidth)`

This function is utilized to generate a Brent-Kung adder and its associated components. It creates instances of classes such as Black, Gray, PG, BitwisePGLogic, GroupPGLogic, SumLogic, and BrentKungAdder, and writes each generated SystemVerilog module using `write_module`.

### Parameters, write_bk

- `file_path`: The file path where all associated Brent-Kung adder SystemVerilog files will be saved.
- `buswidth`: The width of the buses for which the Brent-Kung adder is generated.

These functions are critical in automated hardware design systems, where complex modules like multipliers and adders can be generated programmatically based on design parameters like bus width.

---

[Back to Scripts Index](index.md)
