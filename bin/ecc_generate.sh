#!/bin/bash

###################################################################################
# Output File Path
out_path='./ecc_outdir/'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='hamming'

# Bitwidth
buswidth=8

python ecc_generate.py --type $type --path $out_path --buswidth $buswidth

# Bitwidth
buswidth=32

python ecc_generate.py --type $type --path $out_path --buswidth $buswidth