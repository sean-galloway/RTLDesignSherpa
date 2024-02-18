# ECC Wrapper Script

This script serves as a command-line interface for generating Hamming error-correction codes (ECC) for a specified data bus width. It validates the input parameters and leverages the `rtl_generators.utils` library to create the necessary ECC files.

## Script Usage

The script accepts several command-line options to specify the behavior of the ECC generation process:

- `--path`: The output path where the generated files will be stored.
- `--type`: The type of ECC to generate, currently supports only "hamming".
- `--buswidth`: The width of the data bus for which ECC will be generated.

The script ensures that a valid ECC type is selected and that the bus width is greater than two, as required for Hamming code generation.

## Example

Running the script with the following options:

```bash
python3 ecc_wrapper.py --path /output/path --type hamming --buswidth 16
```

---

[Back to Scripts Index](index.md)

---
