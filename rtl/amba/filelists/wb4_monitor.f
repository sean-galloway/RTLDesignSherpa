# Filelist for wb4_monitor
# Location: rtl/amba/filelists/wb4_monitor.f

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_wb4_pkg.sv
$REPO_ROOT/rtl/amba/wb4/wb4_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/counter_load_clear.f
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/monitor/apb_monitor_addr_check.sv
$REPO_ROOT/rtl/amba/wb4/wb4_monitor.sv
