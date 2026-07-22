# Filelist for monbus_arbiter
# Location: rtl/amba/filelists/monbus_arbiter.f
#
# Dependency tree for the standalone monbus_arbiter DUT (round-robin
# arbitration over N monitor-bus clients, ACK mode, optional in/out skids).

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_priority_encoder.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/monitor/monbus_arbiter.sv

# NOTE: the val/amba monbus_arbiter_grant_hold_dut test top is NOT listed
# here. It lives in val/amba/filelists/monbus_arbiter_grant_hold_dut.f,
# which -f includes this file. Keeping it out means consumers of this
# component filelist do not inherit a testbench top.
