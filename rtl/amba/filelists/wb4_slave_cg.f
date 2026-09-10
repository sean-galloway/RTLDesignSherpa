# Filelist for wb4_slave_cg
# Location: rtl/amba/filelists/wb4_slave_cg.f

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/wb4_slave.f
-f $REPO_ROOT/rtl/common/filelists/icg.f
-f $REPO_ROOT/rtl/common/filelists/clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/shared/amba_clock_gate_ctrl.sv
$REPO_ROOT/rtl/amba/wb4/wb4_slave_cg.sv
