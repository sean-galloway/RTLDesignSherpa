# Filelist for apb_xbar_monitored
# Location: rtl/integ_amba/filelists/apb_xbar_monitored.f
#
# Integration example: apb_xbar_thin with a monitor on every port.
#
# NOTE ON LAYERING: apb_xbar_thin lives in projects/components/apb_xbar, so this
# example under rtl/ depends on a project area -- the same backwards direction as
# rtl/amba/shared -> projects/components/misc (dma_address_gen). Worth revisiting
# together; for now the dependency is at least declared by -f rather than hidden.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/apb_monitor.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f
# apb_xbar_thin instantiates arbiter_round_robin_weighted but its own filelist
# does not carry it, so it cannot be compiled from that list alone. Declared
# here so this example builds; the real fix belongs in apb_xbar_thin.f, which
# is in the projects tree and out of scope for this change.
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin_weighted.f
-f $REPO_ROOT/projects/components/apb_xbar/rtl/filelists/core/apb_xbar_thin.f

$REPO_ROOT/rtl/integ_amba/examples/apb_xbar_monitored.sv
