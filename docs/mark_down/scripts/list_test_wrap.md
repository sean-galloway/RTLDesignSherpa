# list_test_wrap

The following code provides the functionality of a wrapper script to work with test lists in a Python project. It is designed to perform operations related to test management, specifically finding test commands and generating a JSON file list of tests.

## Code Documentation

1. Performs argument parsing on the command line options
2. Checks for the correct options
3. Calls the TestList class with the correct options

### Inputs/Outputs

#### Command Line Arguments

- `--find`: Takes a string to find test commands by a partial test name.
- `--list`: Specifies the name of the JSON file to be created containing the test list.
- `--path`: Provides the path to the directory containing the tests.

### Internal Functionality

- The script starts with a shebang to indicate the interpreter's path for executing the Python script.
- An `argparse.ArgumentParser` instance is created to facilitate command-line argument parsing.
- Command line arguments `--find`, `--list`, and `--path` are defined for the functionality the script supports.
- The script checks if any arguments were provided, and if not, displays the help message and exits.
- A `TestList` object from the `project_automation.list_test` module is instantiated to handle test listing tasks.
- If the `--find` argument is provided, the `generate_run_test_commands` method of the `TestList` object is called to find and generate the relevant test commands.
- If both `--list` and `--path` arguments are provided, the `create_json_file_from_dirs` method of the `TestList` object is called to generate a JSON file that contains a list of test directories found at the specified path.
- The `if __name__ == '__main__':` construct ensures that `main()` is called only when the script is executed directly and not when imported as a module.
- The `generate_run_test_commands` and `create_json_file_from_dirs` methods functionality depend on their implementation within the `TestList` class which is not shown here.

### Usage

To use this script, you would use the command line to pass the appropriate arguments. For example:

Find test commands using a partial test name:

```sh
list_test_wrap.py --find "partial_test_name"
```

Generate a JSON list of tests specifying a path and output file name:

```sh
list_test_wrap.py --list "level0.json" --path "val/common_cocotb_only/""
```

---

[Back to Scripts Index](index.md)
