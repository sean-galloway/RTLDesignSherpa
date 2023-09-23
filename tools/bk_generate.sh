#!/bin/bash

# Output File Path
out_path='./bk_outputs/08'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
adder_type='brent_kung'

# Bitwidth
bitwidth=8

python brent_kung.py --adder-type $adder_type \
                     --path $out_path \
                     --bitwidth $bitwidth
		     
# Output File Path
out_path='./bk_outputs/16'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
adder_type='brent_kung'

# Bitwidth
bitwidth=16

python brent_kung.py --adder-type $adder_type \
                     --path $out_path \
                     --bitwidth $bitwidth
		     
# Output File Path
out_path='./bk_outputs/32'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
adder_type='brent_kung'

# Bitwidth
bitwidth=32

python brent_kung.py --adder-type $adder_type \
                     --path $out_path \
                     --bitwidth $bitwidth
