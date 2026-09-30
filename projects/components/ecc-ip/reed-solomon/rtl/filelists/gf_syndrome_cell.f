# Filelist for gf_syndrome_cell
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_syndrome_cell.f
#
# One Horner accumulator: gf_mul_const by the root plus a register. Uses
# `ALWAYS_FF_RST, so reset_defs.svh must be on the include path first.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul_const.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_syndrome_cell.sv
