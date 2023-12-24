# Run Test Wrapper

The following Python script, `run_test_wrap.py`, is a wrapper used to execute one or multiple tests within a testing framework by leveraging the functionality provided by the `RunTest` class from the `project_automation.run_test` module.

## Usage

This script is run from the command line with various parameters to control the execution of the tests.

### Run a Single Test

```python
python run_test_wrap.py --test my_test --tag my_tag --seed 1234 --params N=8,M=16
```

### Run a List of Tests from Configuration

```python
python run_test_wrap.py --testlist my_test_list --tag my_tag
```

## Command-Line Options

- `--test` <type=str>: Name of the single test to run.
- `--testlist` <type=str>: Name of the file containing a list of tests to run.
- `--tag` <type=str>: A string to tag the test run for identification, with a default value 'run test'.
- `--seed` <type=str>: A seed value to be used in the test, applicable if the test requires randomization, default is `None`.
- `--params` <type=str>: A string of comma-separated key-value pairs passed as test parameters, in the format `key1=value1,key2=value2,...`, default is `None`.

## Internal Functionality

The python script begins by importing required modules and defining the `parse_params` function:

### `parse_params(param_str)`

- Inputs: A string `param_str` containing comma-separated key-value pairs.
- Outputs: A dictionary with the keys and values parsed from the input string.

Next, the script checks if executed as the main program. If so, it parses command-line arguments:

1. An instance of `ArgumentParser` from the `argparse` module is initialized with a description of the script.
2. Command-line arguments are added for `--test`, `--testlist`, `--tag`, `--seed`, and `--params`.
3. The command-line options are parsed into the `args` namespace.

Then, the script performs the following:

- Converts the `params` argument string to a dictionary if provided.
- If `--test` is provided:
  - An instance of `RunTest` is created with a single test name, tag, seed, and parameters.
  - `run_test()` method of the `RunTest` object is called to execute the specified test.
- If `--testlist` is provided:
  - An instance of `RunTest` is created with a test list and tag.
  - `run_test_list()` method of the `RunTest` object is called to execute tests from the provided test list.
- Prints an error message if neither `--test` nor `--testlist` are provided.

**Note:** The actual implementation of the `RunTest` class and its methods (`run_test()` and `run_test_list()`) is assumed to be part of the `project_automation.run_test` module, which is imported at the beginning of the script. The details of this implementation are not provided here.

---

[Back to Scripts Index](index.md)
