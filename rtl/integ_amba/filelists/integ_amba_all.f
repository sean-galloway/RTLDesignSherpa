# ==============================================================================
# RTL integ_amba - master filelist for lint
# ==============================================================================
# Usage: verilator --lint-only -f filelists/integ_amba_all.f
#
# The AMBA integration examples. Library blocks arrive through each module's own
# list, never hand-listed.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/integ_amba/filelists/apb4_peripheral_subsystem.f
-f $REPO_ROOT/rtl/integ_amba/filelists/apb4_xbar_monitored.f
