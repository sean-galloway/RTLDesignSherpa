# ==============================================================================
# MERLIN - Master Filelist
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns.  The ISA
# package and the decode / immediate-generator / ALU blocks are
# common-rv32i's (shared with kestrel/gatling) and come in through
# $RV32I_COMMON_ROOT; this list never hand-lists them.
#
# `-f` includes each block's own filelist; never hand-list sources here.
# ==============================================================================

-f $RV32I_COMMON_ROOT/rtl/filelists/rv32i_common_all.f
-f $MERLIN_ROOT/rtl/filelists/merlin_pkg.f
-f $MERLIN_ROOT/rtl/filelists/fub/merlin_fubs.f
