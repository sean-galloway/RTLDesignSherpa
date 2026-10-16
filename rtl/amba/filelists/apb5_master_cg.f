# Filelist for apb5_master_cg
# Location: rtl/amba/filelists/apb5_master_cg.f
#
# Generated from the inline verilog_sources lists in val/amba.
# Compile order is significant and preserved from the original tests.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/counter_load_clear.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
# APB5 *CHK generation/checking (IHI 0024E ch. 5)
-f $REPO_ROOT/rtl/common/filelists/dataint_parity.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
# amba_clock_gate_ctrl owns its closure (reset_sync, icg, clock_gate_ctrl): -f, never hand-list
-f $REPO_ROOT/rtl/amba/filelists/amba_clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/apb5/apb5_master.sv
$REPO_ROOT/rtl/amba/apb5/apb5_master_cg.sv
