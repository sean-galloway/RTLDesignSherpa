# ==============================================================================
# KESTREL - Master Filelist
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns. Verified
# when written: every module-declaring .sv under rtl/ is reachable from
# the lists below, with no orphans and no duplicate module names.
#
# `-f` includes each block's own filelist; never hand-list sources here.
# ==============================================================================

-f $KESTREL_ROOT/rtl/filelists/kestrel_pkg.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_regfile.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_alu.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_imm_gen.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_decode.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_mem_loader.f
-f $KESTREL_ROOT/rtl/filelists/top/kestrel_core.f
