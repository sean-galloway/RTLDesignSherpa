---
title: List test wrap
layout: docs
date: 2024-01-02
categories: ["script"]
---

The following code provides the functionality of a wrapper script to work with test lists in a Python project. It is designed to perform operations related to test management, specifically finding test commands and generating a JSON file list of tests.

## Code Documentation

1. Performs argument parsing on the command line options

2. Check for the correct options

3. Calls the TestList class with the correct options

### Usage to find a test

To use this script, you would use the command line to pass the appropriate arguments. For example:

Find test commands using a partial test name:

```sh
list_test_wrap.py --find "partial_test_name"

```

### Usage to generate a JSON list of tests specifying a path and output file name

```sh
python3 bin/list_test_wrap.py --list val/testlists/level0.json --path val/common_level0/
python3 bin/list_test_wrap.py --list val/testlists/level1.json --path val/common_level1/

```

### Inputs/Outputs

#### Command Line Arguments

- `--find`: Takes a string to find test commands by a partial test name.

- `--list`: Specifies the name of the JSON file to contain the test list.

- `--path`: Provides the path to the directory containing the tests.

### Internal Functionality

- The script starts with a shebang to indicate the interpreter's path for executing the Python script.

- An `argparse.ArgumentParser` instance facilitates command-line argument parsing.

- Command line arguments `--find`, `--list`, and `--path`

- The script checks for any arguments and, if not provided, displays the help message and exits.

- A `TestList` object from the `project_automation.list_test` module is instantiated to handle test listing tasks.

- If the `--find` argument is provided, the `generate_run_test_commands` method of the `TestList` object is called to find and generate the relevant test commands.

- If both `--list` and `--path` arguments are provided, the `create_json_file_from_dirs` method of the `TestList` object is called to generate a JSON file that contains a list of test directories found at the specified path.

- The `if _*name*_ == '**main**':` construct ensures that `main()` is called only when the script is executed directly and not when imported as a module.

- The `generate_run_test_commands` and `create_json_file_from_dirs` methods functionality depends on their implementation within the `TestList` class, which is not shown here.

---

[Back to Scripts Index](index)

---
