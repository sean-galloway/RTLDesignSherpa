# ==============================================================================
# RTL integ_common - master filelist for lint
# ==============================================================================
# Usage: verilator --lint-only -f filelists/integ_common_all.f
#
# Integration examples: they wire rtl/common blocks together to show a pattern.
# The library blocks arrive through each module's own list, never hand-listed.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/integ_common/filelists/fifo_sync_multi.f
-f $REPO_ROOT/rtl/integ_common/filelists/fifo_sync_multi_sigmap.f
