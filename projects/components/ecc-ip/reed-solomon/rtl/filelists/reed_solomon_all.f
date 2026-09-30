# Master filelist for the reed-solomon component
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/reed_solomon_all.f
#
# The lint closure for rtl/Makefile (AREA := reed_solomon). Every module in
# the component appears here through its own list. Level 0 GF layer today;
# the encoder and decoder blocks join as they land.

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_pkg.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_mul_const.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_mul.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_inv.sv
