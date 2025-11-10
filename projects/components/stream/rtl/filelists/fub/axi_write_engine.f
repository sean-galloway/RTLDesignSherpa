# Filelist for axi_write_engine module
# Location: projects/components/stream/rtl/filelists/fub/axi_write_engine.f

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# AXI write engine module
$STREAM_ROOT/rtl/fub/axi_write_engine.sv
