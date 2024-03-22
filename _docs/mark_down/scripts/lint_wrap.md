---
title: Lint wrap
layout: docs
date: 2024-01-02
categories: ["script"]
---

The `lint_wrap` script at `lint_wrap.py` lints and formats Verilog files using supporting functions encapsulated in a `Lint` class. This script acts as a command-line interface (CLI) utility for code maintenance. The utility offers the option to format the code, perform linting, or do both depending on the passed command-line arguments.

![Lint Wrap UML](../../images_scripts_uml/bin_lint_wrap.svg)

## Usage

The script provides two command-line options:

- `--format`: Formats Verilog files using the `run_verible_format()` method of the `Lint` class.

- `--lint`: Lints Verilog files using the `run_lint()` method of the `Lint` class.

When invoking this script from the command line, a user must specify at least one of the options above; if neither is specified, the script will display an error message prompting for one of the options.

## Code Dependencies and Execution Flow

This script is dependent on the following external modules and classes:

- `argparse` for parsing command-line arguments.

- `Lint` class from `project_automation.lint` module, presumably providing `run_verible_format()` and `run_lint()` methods to format and lint Verilog files, respectively.

The main function of the script performs the following steps:

1\. Create an `ArgumentParser` object with a description that explains the script's purpose.

2\. Defines two mutually non-exclusive command-line arguments (`--format` and `--lint`).

3\. Parses the command-line arguments.

4\. Check if at least one of the arguments above is present; if not, it displays an error message.

5\. Create a `Lint` object for formatting and linting operations.

6\. Calls the `run_verible_format()` method of the `Lint` object if the `--format` argument is set.

7\. Calls the `run_lint()` method of the `Lint` object if the `--lint` argument is set.

## Execution

To run this script, navigate to the directory containing `lint_wrap.py` and use one of the following command-line syntaxes depending on your requirements:
If it differs, Please replace `python3` with your specific Python version command.

## Internal Functionality

The script does not directly perform formatting or linting but delegates these tasks to the `Lint` class's methods. This kind of abstraction is beneficial as it allows for potential extensions of linting and formatting capabilities without modifying the CLI interface script.

**Note:** The script assumes the availability of the `project_automation.lint` module and the proper functioning of its `Lint` class. For comprehensive usage, these dependencies should be appropriately installed and configured.

---

[Back to Scripts Index](index)

---
