# Filelist for axil5_master_rd_cg
# Location: rtl/amba/filelists/axil5_master_rd_cg.f
#
# Same dependency set as the AXI4-Lite wrapper it mirrors: the ICG chain plus
# the base transport module. The optional signal groups ride in the SKID
# payload and add no modules.

+incdir+$REPO_ROOT/rtl/amba/includes

# amba_clock_gate_ctrl owns its closure (reset_sync, icg, clock_gate_ctrl): -f, never hand-list
-f $REPO_ROOT/rtl/amba/filelists/amba_clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/axil5/axil5_master_rd.sv
$REPO_ROOT/rtl/amba/axil5/axil5_master_rd_cg.sv
