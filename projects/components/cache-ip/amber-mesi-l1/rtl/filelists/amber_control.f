# Filelist for amber_control
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_control.f
#
# Blocking-pipeline control FSM (MAS ch02_blocks/01). Flops with reset, so
# the reset macro header comes first, then the package, then the module.
# Instantiates the pending-fill bypass leaf, so its filelist is included
# first (it carries the shared package include itself).

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# Pending-fill bypass register (instantiated by amber_control)
-f $AMBER_ROOT/rtl/filelists/amber_pending_fill_bypass.f

$AMBER_ROOT/rtl/fub/amber_control.sv
