# ==============================================================================
# AMBER - Master Filelist
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns. Verified when
# written: every module-declaring .sv under rtl/ is reachable from the lists
# below, with no orphans and no duplicate module names.
#
# `-f` includes each block's own filelist; never hand-list sources here.
# ==============================================================================

# Shared package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# Standalone test/utility block
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_snoop_kmap_test.f

# Plane restructure filelists (Task 1-3)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_cpu_plane.f
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_coh_core.f
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_axi4_plane.f
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_ace_plane.f

# amber area tops
-f $AMBER_ROOT/rtl/filelists/amber_top.f
-f $AMBER_ROOT/rtl/filelists/amber_pair_fabric.f
-f $AMBER_ROOT/rtl/filelists/amber_ace_top.f
