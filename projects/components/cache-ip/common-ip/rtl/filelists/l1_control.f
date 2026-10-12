# Filelist for l1_control
# Location: projects/components/cache-ip/common-ip/rtl/filelists/l1_control.f
#
# Blocking-pipeline control FSM (MAS ch02_blocks/01). Flops with reset, so
# the reset macro header comes first, then the package, then the module.
# Instantiates the pending-fill bypass leaf, so its filelist is included
# first (it carries the shared package include itself).

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# Pending-fill bypass register (instantiated by l1_control)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pending_fill_bypass.f

# Depth-1 victim buffer (instantiated by l1_control)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_victim.f

$CACHE_COMMON_ROOT/rtl/fub/l1_control.sv
