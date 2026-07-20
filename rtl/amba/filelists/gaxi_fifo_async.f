# Filelist for gaxi_fifo_async
# Location: rtl/amba/filelists/gaxi_fifo_async.f
#
# Gray/Johnson-pointer asynchronous FIFO and its rtl/common submodules.
# This is the base source set shared by the async buffer tests: the skid
# variant (gaxi_skid_buffer_async) layers its own two files on top of this.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

$REPO_ROOT/rtl/common/find_first_set.sv
$REPO_ROOT/rtl/common/find_last_set.sv
$REPO_ROOT/rtl/common/leading_one_trailing_one.sv
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/counter_johnson.sv
$REPO_ROOT/rtl/common/gray2bin.sv
$REPO_ROOT/rtl/common/counter_bingray.sv
$REPO_ROOT/rtl/common/johnson2bin.sv
$REPO_ROOT/rtl/common/glitch_free_n_dff_arn.sv
$REPO_ROOT/rtl/common/fifo_control.sv

$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_async.sv
