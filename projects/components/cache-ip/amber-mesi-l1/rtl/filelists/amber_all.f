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

# Leaf FUBs (first RTL slice, 2026-10-06)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_snoop_kmap_test.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_tag_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_data_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_repl.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_snoop_resp.f

# Control-plane and datapath blocks (stubs filled by later tasks)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_control.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pending_fill_bypass.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_fill.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_drain.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_frontend.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_core.f
-f $AMBER_ROOT/rtl/filelists/amber_top.f
-f $AMBER_ROOT/rtl/filelists/amber_pair_fabric.f
-f $AMBER_ROOT/rtl/filelists/amber_ace_issue.f
-f $AMBER_ROOT/rtl/filelists/amber_ace_top.f
