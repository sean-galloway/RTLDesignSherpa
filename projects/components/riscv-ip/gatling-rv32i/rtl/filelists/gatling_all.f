# ==============================================================================
# GATLING - Master Filelist
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns.  Every
# module-declaring .sv under rtl/ is reachable from the lists below.  The
# ISA package and the decode / immediate-generator / ALU blocks are
# common-rv32i's (shared with kestrel) and come in through gatling_core.f.
#
# `-f` includes each block's own filelist; never hand-list sources here.
# ==============================================================================

-f $GATLING_ROOT/rtl/filelists/fub/gatling_regfile.f
-f $GATLING_ROOT/rtl/filelists/fub/gatling_mem_bram.f
-f $GATLING_ROOT/rtl/filelists/top/gatling_core.f
