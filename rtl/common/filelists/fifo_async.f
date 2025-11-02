# Filelist for fifo_async module
# Location: rtl/common/filelists/fifo_async.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Dependencies
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/gray2bin.sv
$REPO_ROOT/rtl/common/bin2gray.sv

$REPO_ROOT/rtl/common/counter_bingray.sv
$REPO_ROOT/rtl/common/glitch_free_n_dff_arn.sv
# fifo_async module
$REPO_ROOT/rtl/common/fifo_async.sv
