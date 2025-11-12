# Filelist for sram_controller module
# Location: projects/components/stream/rtl/filelists/fub/sram_controller.f

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Dependencies - GAXI FIFO and simple SRAM
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv


# Stream components - allocation controller and latency bridge
$STREAM_ROOT/rtl/fub/stream_alloc_ctrl.sv
$STREAM_ROOT/rtl/fub/stream_drain_ctrl.sv
$STREAM_ROOT/rtl/fub/stream_latency_bridge.sv

# SRAM controller unit (single channel: alloc_ctrl + FIFO + latency bridge)
$STREAM_ROOT/rtl/fub/sram_controller_unit.sv

# SRAM controller top-level (must be last - instantiates units)
$STREAM_ROOT/rtl/fub/sram_controller.sv
