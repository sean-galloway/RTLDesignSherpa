# Filelist for axi5_atomic_rr_tracker
# Location: rtl/amba/filelists/axi5_atomic_rr_tracker.f
#
# Declares the complete compile closure for this component. Standalone:
# no sub-blocks, no package imports.

# reset_defs.svh -- the module uses `ALWAYS_FF_RST, so its macro header
# must be on the include path and compiled before it.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$REPO_ROOT/rtl/amba/axi5/axi5_atomic_rr_tracker.sv
