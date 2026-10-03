# Filelist for chien_search
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/chien_search.f
#
# Level 2: t+1 Chien cells (two gf_mul_const each). Uses `ALWAYS_FF_RST.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul_const.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/fub/chien_search.sv
