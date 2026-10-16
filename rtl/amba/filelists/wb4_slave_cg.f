# Filelist for wb4_slave_cg
# Location: rtl/amba/filelists/wb4_slave_cg.f

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/wb4_slave.f
# amba_clock_gate_ctrl owns its closure (reset_sync, icg, clock_gate_ctrl): -f, never hand-list
-f $REPO_ROOT/rtl/amba/filelists/amba_clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/wb4/wb4_slave_cg.sv
