# Filelist for onyx_ccu
# Location: projects/components/cache-ip/onyx-ace-ccu/rtl/filelists/onyx_ccu.f
#
# The onyx coherency unit v1 (onyx TASK-001 step 2): the jet-prime pair
# fabric generalized to N ports under the PRD's D rulings. Self-contained
# RTL: only the shared package and the reset macros.

# Reset macros
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared cache-ip package (l1_pkg: geometry + ACE request classes)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# The unit
$ONYX_ROOT/rtl/top/onyx_ccu.sv
