---
title: Run Test Wrapper
layout: docs
date: 2024-01-02
categories: ["script"]
---

The following Python script, `run_test_wrap.py`, is a wrapper used to execute one or multiple tests within a testing framework by leveraging the functionality provided by the `RunTest` class from the `project_automation.run_test` module.

## Usage

This script runs from the command line with various parameters to control the execution of the tests.

### Run a Single Test

```python

python bin/run_test_wrap.py --test my_test --tag my_tag --seed 1234 --params N=8,M=16

```

### Run a List of Tests from Configuration

```python

python bin/run_test_wrap.py --testlist my_test_list --tag my_tag

```

### Usage to run a Level 0 regression, with and without randomization

```sh
python3 bin/run_test_wrap.py --testlist level0 --tag 20240218 --short_name

python3 bin/run_test_wrap.py --testlist level0 --tag 20240218_rand --randomize --short_name

```

## Command-Line Options

- `--test` \<type=str>: Name of the single test to run.

- `--testlist` \<type=str>: The file containing a list of tests to run.

- `--tag` \<type=str>: A string to tag the test run for identification, with a default value 'run test'.

- `--seed` \<type=str>: A seed value used in the test, applicable if the test requires randomization; default is `None`.

- `--params` \<type=str>: A string of comma-separated key-value pairs passed as test parameters in the format `key1=value1,key2=value2,...`, default is `None`.

- `--randomize` \<type=Boolean>: A simple flag to indicate to use of random seeds on the regression; default is `False`.

- `--short_name` \<type=Boolean>: A simple flag to indicate to use of test name that only has the seed as an extension default is `True`.

## Internal Functionality

The Python script begins by importing the required modules and defining the `parse_params` function:

### `parse_params(param_str)`

- Inputs: A string `param_str` containing comma-separated key-value pairs.

- Outputs: A dictionary with the keys and values parsed from the input string.

Next, the script checks if executed as the main program. If so, it parses command-line arguments:

1. An instance of `ArgumentParser` from the `argparse` module initialized with the script.

2. Command-line arguments are added for `--test`, `--testlist`, `--tag`, `--seed`, and `--params`.

3. The command-line options are parsed into the `args` namespace.

Then, the script performs the following:

- Converts the `params` argument string to a dictionary if provided.

- If `--test` is provided:

- An instance of `RunTest` is created with a single test name, tag, seed, and parameters.

- The `run_test()` method of the `RunTest` object is called to execute the specified test.

- If `--testlist` is provided:

- An instance of `RunTest` is created with a test list and tag.

- The `run_test_list()` method of the `RunTest` object is called to execute tests from the provided test list.

- Prints an error message if neither `--test` nor `--testlist` is provided.

**Note:** The actual implementation of the `RunTest` class and its methods (`run_test()` and `run_test_list()`) is assumed to be part of the `project_automation.run_test` module, which is imported at the beginning of the script. The details of this implementation are not provided here; the links are TODO.

---

[Back to Scripts Index](index)

---
