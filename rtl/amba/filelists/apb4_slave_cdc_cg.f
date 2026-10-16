# Filelist for apb4_slave_cdc_cg
# Location: rtl/amba/filelists/apb4_slave_cdc_cg.f
#
# CDC is a gray-pointer async FIFO (gaxi_fifo_async), not a toggle handshake:
# pointers are absolute positions and each domain resets its own pointer plus
# its crossed copy of the remote pointer, so an independent reset of one side
# cannot fabricate or swallow a transfer.  Both FIFO sides run on the GATED
# clocks, so gating cannot reorder or drop a queued transfer.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh


$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f

# amba_clock_gate_ctrl owns its closure (reset_sync, icg, clock_gate_ctrl): -f, never hand-list
-f $REPO_ROOT/rtl/amba/filelists/amba_clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/apb4/apb4_slave.sv
$REPO_ROOT/rtl/amba/apb4/apb4_slave_cdc_cg.sv
