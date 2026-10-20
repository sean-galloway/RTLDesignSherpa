# Filelist for sram_controller_unit
# Location: projects/components/dma-ip/stream/rtl/filelists/fub/sram_controller_unit.f
#
# Created 2026-10-19 so formal/stream/sram_controller_unit builds its flat from this closure
# (make/formal_flat.mk) instead of a hand-listed SRCS.

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$STREAM_ROOT/rtl/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
$STREAM_ROOT/rtl/includes/stream_pkg.sv
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $STREAM_ROOT/rtl/filelists/fub/stream_latency_bridge.f
$STREAM_ROOT/rtl/fub/stream_alloc_ctrl.sv
$STREAM_ROOT/rtl/fub/stream_drain_ctrl.sv
$STREAM_ROOT/rtl/fub/sram_controller_unit.sv
