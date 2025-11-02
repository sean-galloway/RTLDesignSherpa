# Filelist for descriptor_engine module
# Location: projects/components/stream/rtl/filelists/fub/descriptor_engine.f

# Include directories
+incdir+$REPO_ROOT/projects/components/stream/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/stream/rtl/includes/stream_pkg.sv

# Dependencies - GAXI FIFO and skid buffer
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Descriptor engine module
$REPO_ROOT/projects/components/stream/rtl/stream_fub/descriptor_engine.sv
