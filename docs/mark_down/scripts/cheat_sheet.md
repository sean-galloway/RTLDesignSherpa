# Cheat Sheet for the main scripts

The main scripts take care of the command line parsing and simply instantiate the underlying classes which do all of the real work.

This document will evolve as more scripts are added, showing the most common use cases for the scripts.

## lint_wrap.py

The `lint_wrap` script located at `./bin/lint_wrap.py` is designed to lint and format Verilog files using supporting functions encapsulated in a `Lint` class. This script acts as a command-line interface (CLI) utility for code maintenance purposes. The utility offers the options:

```sh
bin/lint_wrap.py --format
bin/lint_wrap.py --lint
bin/lint_wrap.py --format --lint
```

The format option uses verible format to ensure all of the code follows a convention. The lint option actually runs verible lint. Verible issues can be waived like this:

```verilog
    parameter INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
```

## list_test_wrap.py

The following code provides the functionality of a wrapper script to work with test lists in a Python project. It is designed to perform operations related to test management, specifically finding test commands and generating a JSON file list of tests.

Find test commands using a partial test name:

```sh
bin/list_test_wrap.py --find "add"
```

output:

```sh
python run_test_wrap.py --test val/common_cocotb_only/math_adder_brent_kung_008 --tag my_tag --seed 1234
python run_test_wrap.py --test val/common_cocotb_only/math_adder_brent_kung_016 --tag my_tag --seed 1234
python run_test_wrap.py --test val/common_cocotb_only/math_adder_brent_kung_032 --tag my_tag --seed 1234
python run_test_wrap.py --test val/common_cocotb_only/math_adder_carry_lookahead --tag my_tag --seed 1234 --params N=4
python run_test_wrap.py --test val/common_cocotb_only/math_adder_carry_save --tag my_tag --seed 1234
python run_test_wrap.py --test val/common_cocotb_only/math_adder_carry_save_nbit --tag my_tag --seed 1234 --params N=4
python run_test_wrap.py --test val/common_cocotb_only/math_adder_full --tag my_tag --seed 1234
python run_test_wrap.py --test val/common_cocotb_only/math_adder_full_nbit --tag my_tag --seed 1234 --params N=4
python run_test_wrap.py --test val/common_cocotb_only/math_adder_half --tag my_tag --seed 1234
python run_test_wrap.py --test val/common_cocotb_only/math_adder_hierarchical --tag my_tag --seed 1234 --params N=16,C=6
python run_test_wrap.py --test val/common_cocotb_only/math_adder_kogge_stone_nbit --tag my_tag --seed 1234 --params N=4
python run_test_wrap.py --test val/common_cocotb_only/math_adder_ripple_carry --tag my_tag --seed 1234 --params N=4
python run_test_wrap.py --test val/common_cocotb_only/math_addsub_full_nbit --tag my_tag --seed 1234 --params N=8

```

Generate a JSON list of tests specifying a path and output file name (for each bin of tests, level0, level1, etc, there is an associated in ./val/testlists/level0.json. These json files contain the parameters and the seed used for the test. This is hard to grab manually.):

```sh
bin/list_test_wrap.py --list "level0.json" --path "val/common_cocotb_only/"
```

Here is an example of the json file:

```python
{
    "rtl_dirs": [
                    "rtl/common", 
                    "rtl/xilinx"
                ],
    "test_lists": {
                "level0": "val/testlists/level0.json"
                },
    "make_clean" : "val/common_cocotb_only/cleanall.mk",
    "lint_reports": {"lint":"./reports/lint/", "verible":"./reports/verible/"}
}
```

## run_test_wrap.py

The following Python script, `run_test_wrap.py`, is a wrapper used to execute one or multiple tests within a testing framework by leveraging the functionality provided by the `RunTest` class from the `project_automation.run_test` module. It does this by using the levelX.json file to know the parameters and the seed.
Examples:

```sh
# run one test
bin/run_test_wrap.py --test val/common_cocotb_only/arbiter_round_robin --tag 122423 --seed 1234 --params CLIENTS=6

# run level0
bin/run_test_wrap.py --testlist level0 --tag 122423
```

For the level0 regression, a directory called regression is created at the repo_root level. Inside of this is another directory called "tag" to hold all of this run together.

## math_generate.py

This generates the various kinds of math structures: BrentKung, Wallace, Dadda. Here is an example of a BrentKung:

```sh
out_path='./math_outputs/bk_08'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='brent_kung'

# Bitwidth
buswidth=8

bin/math_generate.py --type $type --path $out_path --buswidth $buswidth
```

---

[Back to Scripts Index](index.md)
