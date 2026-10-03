# Filelist for ribm_pe
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/ribm_pe.f
#
# One riBM processing element: two gf_mul and two registers. Uses
# `ALWAYS_FF_RST, so reset_defs.svh must be on the include path first.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/fub/gf/ribm_pe.sv
