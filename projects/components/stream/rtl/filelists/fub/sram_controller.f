# Filelist for sram_controller module
# Location: projects/components/stream/rtl/filelists/fub/sram_controller.f

# Include directories
+incdir+$REPO_ROOT/projects/components/stream/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/stream/rtl/includes/stream_pkg.sv

# Dependencies - GAXI FIFO and simple SRAM
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/projects/components/stream/rtl/stream_fub/simple_sram.sv

# SRAM controller module
$REPO_ROOT/projects/components/stream/rtl/stream_fub/sram_controller.sv
