#!/bin/bash

###################################################################################
# Output File Path
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

python math_generate.py --type $type --path $out_path --buswidth $buswidth

# Output File Path
out_path='./math_outputs/bk_16'

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
buswidth=16

python math_generate.py --type $type --path $out_path --buswidth $buswidth

# Output File Path
out_path='./math_outputs/bk_32'

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
buswidth=32

python math_generate.py --type $type --path $out_path --buswidth $buswidth


###################################################################################
# Output File Path
out_path='./math_outputs/dad_08'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='dadda'

# Bitwidth
buswidth=8

python math_generate.py --type $type --path $out_path --buswidth $buswidth

# Output File Path
out_path='./math_outputs/dad_16'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='dadda'

# Bitwidth
buswidth=16

python math_generate.py --type $type --path $out_path --buswidth $buswidth

# Output File Path
out_path='./math_outputs/dad_32'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='dadda'

# Bitwidth
buswidth=32

python math_generate.py --type $type --path $out_path --buswidth $buswidth


###################################################################################
# Output File Path
out_path='./math_outputs/walfa_08'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='wallace_fa'

# Bitwidth
buswidth=8

python math_generate.py --type $type --path $out_path --buswidth $buswidth

# Output File Path
out_path='./math_outputs/walfa_16'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='wallace_fa'

# Bitwidth
buswidth=16

python math_generate.py --type $type --path $out_path --buswidth $buswidth

# Output File Path
out_path='./math_outputs/walfa_32'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='wallace_fa'

# Bitwidth
buswidth=32

python math_generate.py --type $type --path $out_path --buswidth $buswidth


###################################################################################
# Output File Path
out_path='./math_outputs/walcsa_08'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='wallace_csa'

# Bitwidth
buswidth=8

python math_generate.py --type $type --path $out_path --buswidth $buswidth

# Output File Path
out_path='./math_outputs/walcsa_16'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='wallace_csa'

# Bitwidth
buswidth=16

python math_generate.py --type $type --path $out_path --buswidth $buswidth

# Output File Path
out_path='./math_outputs/walcsa_32'

if [ ! -d "$out_path" ]; then
    mkdir -p "$out_path"
    echo "Directory '$out_path' created."
else
    echo "Directory '$out_path' already exists."
fi
rm -f $out_path/*

# Adder Type
type='wallace_csa'

# Bitwidth
buswidth=32

python math_generate.py --type $type --path $out_path --buswidth $buswidth