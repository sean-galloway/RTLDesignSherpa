# Filelist for gaxi_fifo_async
# Location: rtl/cdc/filelists/gaxi_fifo_async.f
#
# Gray/Johnson-pointer asynchronous FIFO and its rtl/common submodules.
# This is the base source set shared by the async buffer tests: the skid
# variant (gaxi_skid_buffer_async) layers its own two files on top of this.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

-f $REPO_ROOT/rtl/common/filelists/find_first_set.f
-f $REPO_ROOT/rtl/common/filelists/find_last_set.f
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_johnson.f
-f $REPO_ROOT/rtl/cdc/filelists/gray2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_bingray.f
-f $REPO_ROOT/rtl/cdc/filelists/johnson2bin.f
-f $REPO_ROOT/rtl/common/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f

$REPO_ROOT/rtl/cdc/gaxi_fifo_async.sv
