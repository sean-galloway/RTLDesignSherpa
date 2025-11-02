# Filelist for fifo_sync module
# Location: rtl/common/filelists/fifo_sync.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Dependencies
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# fifo_sync module
$REPO_ROOT/rtl/common/fifo_sync.sv
