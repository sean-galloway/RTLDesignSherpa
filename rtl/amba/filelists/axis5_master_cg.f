# Filelist for axis5_master_cg
# Location: rtl/amba/filelists/axis5_master_cg.f
#
# Generated from the inline verilog_sources lists in val/amba.
# Compile order is significant and preserved from the original tests.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/common/filelists/icg.f
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/counter_load_clear.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
# dataint_parity -- computes/checks every AXI5-Stream *CHK bit (IHI 0051B ch. 5)
-f $REPO_ROOT/rtl/common/filelists/dataint_parity.f
-f $REPO_ROOT/rtl/common/filelists/clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/shared/amba_clock_gate_ctrl.sv
$REPO_ROOT/rtl/amba/axis5/axis5_master.sv
$REPO_ROOT/rtl/amba/axis5/axis5_master_cg.sv
