# Filelist for l1_pending_fill_bypass
# Location: projects/components/cache-ip/common-ip/rtl/filelists/l1_pending_fill_bypass.f
#
# Pending-fill / load-miss bypass register (MAS ch02_blocks/02). Flops with
# reset, so the reset macro header comes first, then the package, then the
# module.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

$CACHE_COMMON_ROOT/rtl/fub/l1_pending_fill_bypass.sv
