# Filelist for rs_erasure_unit
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_erasure_unit.f
#
# The decoder's erasure half (ERASURE_SUPPORT = 1): X record at receive,
# Gamma/GS transform, solver window, combined locator/evaluator.
# Uses `ALWAYS_FF_RST.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul_const.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/fub/rs_erasure_unit.sv
