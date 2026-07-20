# Filelist for apb_slave_cdc_cg
# Location: rtl/amba/filelists/apb_slave_cdc_cg.f
#
# CDC is a gray-pointer async FIFO (gaxi_fifo_async), not a toggle handshake:
# pointers are absolute positions and each domain resets its own pointer plus
# its crossed copy of the remote pointer, so an independent reset of one side
# cannot fabricate or swallow a transfer.  Both FIFO sides run on the GATED
# clocks, so gating cannot reorder or drop a queued transfer.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

$REPO_ROOT/rtl/common/icg.sv
$REPO_ROOT/rtl/common/clock_gate_ctrl.sv
$REPO_ROOT/rtl/common/gray2bin.sv
$REPO_ROOT/rtl/common/counter_bingray.sv
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/counter_johnson.sv
$REPO_ROOT/rtl/common/glitch_free_n_dff_arn.sv
$REPO_ROOT/rtl/common/find_first_set.sv
$REPO_ROOT/rtl/common/find_last_set.sv
$REPO_ROOT/rtl/common/leading_one_trailing_one.sv
$REPO_ROOT/rtl/common/johnson2bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_async.sv

$REPO_ROOT/rtl/amba/shared/amba_clock_gate_ctrl.sv
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc_cg.sv
