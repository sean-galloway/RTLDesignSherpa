# Filelist for axi_monitor_reporter
# Location: rtl/amba/filelists/axi_monitor_reporter.f
#
# Created 2026-10-19 so formal/amba/axi_monitor_reporter builds its flat from this closure
# (make/formal_flat.mk) instead of a hand-listed SRCS.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_error.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_timeout.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_compl.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_threshold.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_perf.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_debug.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter.sv
