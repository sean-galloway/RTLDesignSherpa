# Filelist for axi_monitor_pktgen_dut
# Location: rtl/amba/filelists/axi_monitor_pktgen_dut.f
#
# Packet-generation path harness: axi_monitor_timeout + axi_monitor_reporter
# and its six packet-type sub-blocks, wrapped so a testbench can drive the
# transaction table directly. Compile order is significant.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_timeout.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_error.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_timeout.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_compl.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_threshold.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_perf.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_debug.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter.sv
$REPO_ROOT/val/amba/axi_monitor_pktgen_dut.sv
