# Filelist for apb5_slave_cdc_cg
# Location: rtl/amba/filelists/apb5_slave_cdc_cg.f
#
# Generated from the inline verilog_sources lists in val/amba.
# Compile order is significant and preserved from the original tests.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/common/filelists/icg.f
-f $REPO_ROOT/rtl/common/filelists/counter_load_clear.f
-f $REPO_ROOT/rtl/common/filelists/clock_gate_ctrl.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
$REPO_ROOT/rtl/amba/shared/amba_clock_gate_ctrl.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/apb5/apb5_slave.sv
$REPO_ROOT/rtl/amba/apb5/apb5_slave_cdc.sv
$REPO_ROOT/rtl/amba/apb5/apb5_slave_cdc_cg.sv
