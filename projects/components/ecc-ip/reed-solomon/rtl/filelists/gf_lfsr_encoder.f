# Filelist for gf_lfsr_encoder
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_lfsr_encoder.f
#
# The systematic encoder's LFSR: 2t gf_mul_const taps on gf_pkg. Uses
# `ALWAYS_FF_RST, so reset_defs.svh must be on the include path first.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul_const.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_lfsr_encoder.sv
