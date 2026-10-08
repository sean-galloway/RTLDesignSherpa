# Filelist for amber_control
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_control.f
#
# Blocking-pipeline control FSM (MAS ch02_blocks/01). Flops with reset, so
# the reset macro header comes first, then the package, then the module.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

$AMBER_ROOT/rtl/fub/amber_control.sv
