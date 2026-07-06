# Filelist for scheduler module
# Location: projects/components/stream/rtl/filelists/fub/scheduler.f

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# TASK-101 run-base address generator dependencies (USE_ROW_COL_MAJOR_ADDRESSING)
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/projects/components/misc/rtl/dma_address_gen.sv
$STREAM_ROOT/rtl/fub/stream_run_addr_gen.sv

# Scheduler module
$STREAM_ROOT/rtl/fub/scheduler.sv
