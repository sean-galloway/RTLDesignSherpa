# Filelist for arbiter_single_client
# Location: rtl/common/filelists/arbiter_single_client.f
#
# Declares the complete compile closure for this component.

# reset_defs.svh -- the module uses `ALWAYS_FF_RST, so its macro header
# must be on the include path and compiled before it.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$REPO_ROOT/rtl/common/arbiter_single_client.sv
