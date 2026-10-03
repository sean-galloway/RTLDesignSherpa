# Filelist for forney_evaluator
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/forney_evaluator.f
#
# Level 1: t evaluator cells (gf_mul_const), one gf_inv, one gf_mul. Uses
# `ALWAYS_FF_RST.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul_const.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_inv.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/fub/forney_evaluator.sv
