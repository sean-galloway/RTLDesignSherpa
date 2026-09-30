# Filelist for rs_error_injector
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_error_injector.f
#
# Test stimulus block: S inline xorshift32 generators and the injection logic.
# Uses `ALWAYS_FF_RST.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/rs_error_injector.sv
