# Filelist for axil5_slave_rd_cg
# Location: rtl/amba/filelists/axil5_slave_rd_cg.f
#
# Same dependency set as the AXI4-Lite wrapper it mirrors: the ICG chain plus
# the base transport module. The optional signal groups ride in the SKID
# payload and add no modules.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/common/filelists/icg.f
-f $REPO_ROOT/rtl/common/filelists/clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/shared/amba_clock_gate_ctrl.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/axil5/axil5_slave_rd.sv
$REPO_ROOT/rtl/amba/axil5/axil5_slave_rd_cg.sv
