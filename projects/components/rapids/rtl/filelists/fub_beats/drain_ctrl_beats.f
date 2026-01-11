# Filelist for beats_drain_ctrl module (Beats-specific)
# Location: projects/components/rapids/rtl/filelists/fub_beats/drain_ctrl_beats.f
# Purpose: Drain control (Virtual FIFO for data availability tracking)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies from rtl/common/
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# Beats drain control module
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/drain_ctrl_beats.sv
