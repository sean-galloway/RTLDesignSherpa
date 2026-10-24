# ==============================================================================
# KESTREL - Master Filelist
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns. Verified
# when written: every module-declaring .sv under rtl/ is reachable from
# the lists below, with no orphans and no duplicate module names.
#
# The ISA package and the decode / immediate-generator / ALU blocks are
# common-rv32i's (shared with gatling, 2026-10-22) and come in through
# $RV32I_COMMON_ROOT; this list never hand-lists them.
#
# `-f` includes each block's own filelist; never hand-list sources here.
# ==============================================================================

-f $RV32I_COMMON_ROOT/rtl/filelists/rv32i_common_all.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_regfile.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_mem_loader.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_mem_bram.f
-f $KESTREL_ROOT/rtl/filelists/top/kestrel_core.f
