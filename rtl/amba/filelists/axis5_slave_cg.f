# Filelist for axis5_slave_cg
# Location: rtl/amba/filelists/axis5_slave_cg.f
#
# Generated from the inline verilog_sources lists in val/amba.
# Compile order is significant and preserved from the original tests.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/counter_load_clear.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
# dataint_parity -- computes/checks every AXI5-Stream *CHK bit (IHI 0051B ch. 5)
-f $REPO_ROOT/rtl/common/filelists/dataint_parity.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
# amba_clock_gate_ctrl owns its closure (reset_sync, icg, clock_gate_ctrl): -f, never hand-list
-f $REPO_ROOT/rtl/amba/filelists/amba_clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/axis5/axis5_slave.sv
$REPO_ROOT/rtl/amba/axis5/axis5_slave_cg.sv
