# Filelist for apb_peripheral_subsystem
# Location: rtl/integ_amba/filelists/apb_peripheral_subsystem.f
#
# Integration example: an APB peripheral subsystem with a monitor per slave and
# a round-robin arbiter over the monitor bus. It wires library blocks together
# to show a pattern; it is not itself a library module.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/apb_monitor.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f

$REPO_ROOT/rtl/integ_amba/examples/apb_peripheral_subsystem.sv
