# Filelist for fifo_async_div2 module
# Location: rtl/common/filelists/fifo_async_div2.f

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
$REPO_ROOT/rtl/common/counter_johnson.sv
$REPO_ROOT/rtl/common/glitch_free_n_dff_arn.sv
$REPO_ROOT/rtl/common/find_first_set.sv
$REPO_ROOT/rtl/common/find_last_set.sv
$REPO_ROOT/rtl/common/leading_one_trailing_one.sv
$REPO_ROOT/rtl/common/grayj2bin.sv
# fifo_async_div2 module
$REPO_ROOT/rtl/common/fifo_async_div2.sv
