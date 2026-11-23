# ==============================================================================
# PEREGRINE - Master Filelist
# ==============================================================================
# The compile closure for every module this area owns.  `-f` includes each
# block's own filelist; never hand-list sources here.

-f $RV32I_COMMON_ROOT/rtl/filelists/rv32i_common_all.f
-f $PEREGRINE_ROOT/rtl/filelists/peregrine_pkg.f
-f $PEREGRINE_ROOT/rtl/filelists/fub/peregrine_fubs.f
-f $PEREGRINE_ROOT/rtl/filelists/top/peregrine_core.f
