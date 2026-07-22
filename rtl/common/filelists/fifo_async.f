# Filelist for fifo_async module
# Location: rtl/common/filelists/fifo_async.f
#
# fifo_async supports BOTH pointer encodings via USE_JOHNSON, and the choice is
# a parameter rather than a separate module, so this filelist must carry the
# dependencies of both paths:
#   USE_JOHNSON=0 (Gray, default) -> counter_bingray + gray2bin
#   USE_JOHNSON=1 (Johnson)       -> counter_bin + counter_johnson + johnson2bin
# The Johnson set is what the retired fifo_async_div2 module used to pull in.

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Shared dependencies
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/glitch_free_n_dff_arn.sv
$REPO_ROOT/rtl/common/find_first_set.sv
$REPO_ROOT/rtl/common/find_last_set.sv
$REPO_ROOT/rtl/common/leading_one_trailing_one.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# Gray pointer path (USE_JOHNSON=0)
$REPO_ROOT/rtl/common/bin2gray.sv
$REPO_ROOT/rtl/common/gray2bin.sv
$REPO_ROOT/rtl/common/counter_bingray.sv

# Johnson pointer path (USE_JOHNSON=1)
$REPO_ROOT/rtl/common/counter_johnson.sv
$REPO_ROOT/rtl/common/johnson2bin.sv

# fifo_async module
$REPO_ROOT/rtl/common/fifo_async.sv
