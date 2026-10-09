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
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# Leaf FUBs (first RTL slice, 2026-10-06)
-f $AMBER_ROOT/rtl/filelists/amber_snoop_kmap.f
-f $AMBER_ROOT/rtl/filelists/amber_tag_array.f
-f $AMBER_ROOT/rtl/filelists/amber_data_array.f
-f $AMBER_ROOT/rtl/filelists/amber_repl.f
-f $AMBER_ROOT/rtl/filelists/amber_snoop_resp.f

# Control-plane and datapath blocks (stubs filled by later tasks)
-f $AMBER_ROOT/rtl/filelists/amber_control.f
-f $AMBER_ROOT/rtl/filelists/amber_pending_fill_bypass.f
-f $AMBER_ROOT/rtl/filelists/amber_fill.f
-f $AMBER_ROOT/rtl/filelists/amber_drain.f
-f $AMBER_ROOT/rtl/filelists/amber_frontend.f
-f $AMBER_ROOT/rtl/filelists/amber_core.f
-f $AMBER_ROOT/rtl/filelists/amber_top.f
-f $AMBER_ROOT/rtl/filelists/amber_pair_fabric.f
-f $AMBER_ROOT/rtl/filelists/amber_ace_top.f
