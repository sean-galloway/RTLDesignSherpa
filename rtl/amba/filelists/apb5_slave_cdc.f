# Filelist for apb5_slave_cdc
# Location: rtl/amba/filelists/apb5_slave_cdc.f
#
# CDC is a gray-pointer async FIFO (gaxi_fifo_async), not a toggle handshake:
# pointers are absolute positions and each domain resets its own pointer plus
# its crossed copy of the remote pointer, so an independent reset of one side
# cannot fabricate or swallow a transfer.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

-f $REPO_ROOT/rtl/cdc/filelists/gray2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_bingray.f
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_johnson.f
-f $REPO_ROOT/rtl/common/filelists/counter_load_clear.f
-f $REPO_ROOT/rtl/common/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/find_first_set.f
-f $REPO_ROOT/rtl/common/filelists/find_last_set.f
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f
-f $REPO_ROOT/rtl/cdc/filelists/johnson2bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f

-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f

$REPO_ROOT/rtl/amba/apb5/apb5_slave.sv
$REPO_ROOT/rtl/amba/apb5/apb5_slave_cdc.sv
