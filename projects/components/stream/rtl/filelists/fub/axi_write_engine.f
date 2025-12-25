# Filelist for axi_write_engine module
# Location: projects/components/stream/rtl/filelists/fub/axi_write_engine.f

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Dependencies
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# AXI write engine module
$STREAM_ROOT/rtl/fub/axi_write_engine.sv
