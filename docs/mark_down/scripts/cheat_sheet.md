# Cheat Sheet for the main scripts

The main scripts handle the command line parsing and instantiate the underlying classes, which do all the work.

This document will evolve as more scripts get added, showing the most common use cases for the scripts.

## [lint_wrap.py](lint_wrap.md)

The `lint_wrap` script at `lint_wrap.py` is to lint and format Verilog files using supporting functions encapsulated in a `Lint` class. This script acts as a command-line interface (CLI) utility for code maintenance. The utility offers the following options:

```sh

lint_wrap.py --format

lint_wrap.py --lint

lint_wrap.py --format --lint

```

The format option uses a verible format to ensure all code follows a convention. The lint option runs verible lint. Verible issues are available for waivers.

```verilog

parameter INSTANCE_NAME = "DEADF1F0" // verilog_lint: waive explicit-parameter-storage-type

```

## [list_test_wrap.py](list_test_wrap.md)

The following code provides the functionality of a wrapper script to work with test lists in a Python project. It is designed to perform operations related to test management, specifically finding test commands and generating a JSON file list of tests.

Find test commands using a simulation partial test name:

```sh

list_test_wrap.py --find "add"

```

Output:

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

Generate a JSON list of tests specifying a path and output file name (for each bin of tests, level0, level1, etc., there is an associated in ./val/testlists/level0.json. These JSON files contain the parameters and the seed used for the test. Creating the JSON list with the information from the makefile is hard to grab manually.):

```sh

list_test_wrap.py --list "level0.json" --path "val/common_cocotb_only/"

```

Here is an example of the JSON file:

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

## [run_test_wrap.py](run_test_wrap.md)

The following Python script, `run_test_wrap.py`, is a wrapper used to execute one or multiple tests within a testing framework by leveraging the functionality provided by the `RunTest` class from the `project_automation.run_test` module. It uses the levelX.json file to know the parameters and the seed.

Examples:

```sh

# run one test

run_test_wrap.py --test val/common_cocotb_only/arbiter_round_robin --tag 122423 --seed 1234 --params CLIENTS=6

# run level0

run_test_wrap.py --testlist level0 --tag 122423

```

The script creates a regression directory for the level0 regression, the repo_root level. Inside this is another directory called "tag" to hold all this run together.

## [math_generate.py](math_generate.md)

This script generates many versions of math structures: BrentKung, Wallace, and Dadda. Here is an example of a BrentKung:

```sh

out_path='./math_outputs/bk_08'

if [ ! -d "\$out_path" ]; then

mkdir -p "\$out_path"

echo "Directory '\$out_path' created."

else

echo "Directory '\$out_path' already exists."

fi

rm -f \$out_path/*

# Adder Type

type='brent_kung'

# Bitwidth

buswidth=8

math_generate.py --type \$type --path \$out_path --buswidth \$buswidth

```

## [vcd2wavedrom2.py](vcd2wavedrom2.md)

This script generates wavedrom files based on vcd and gtkw files. The gtkw file provides the signal selection, grouping and ordering, and adding hierarchical labels to the signals.

```sh

# Step 0: cd to the area with the simulation

# Step 1: Create the config file

python3 $REPO_ROOT/bin/vcd2wavedrom2.py -i dump.vcd -m config.json     # This will grab all of the signals in the vcd

python3 $REPO_ROOT/bin/vcd2wavedrom2.py -i dump.vcd -m config.json -hl u_weighted_round_robin -f "1290ns" -t "1320ns"   # the -hl specifies a hierarchy to grab from the vcd; one or more may be passed in

# Step 1.5: Update the config file. One may want to remove or reorganize the signals. One may also want to put all of the units into something consistent, like ns.

# Step 2: Generate the wavedrom file

python3 $REPO_ROOT/bin/vcd2wavedrom2.py -i dump.vcd -g debug.gtkw -c config.json -o wavedrom.json    # this is a basic command line, all of the hard stuff is done when making the config file


```

---

[Back to Scripts Index](index.md)

---
