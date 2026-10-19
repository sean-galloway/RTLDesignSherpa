# Filelist for the bus-stress cores (protocol-neutral; AXI4 on the fub side)
# Location: rtl/amba/filelists/axi_stress_core.f
#
# The traffic generators / checkers every protocol shell of the stress master
# and slave is built on. Consumers -f the shell's filelist, not this one.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/axi_stress_pkg.sv
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

$REPO_ROOT/rtl/amba/shared/axi_stress_ord_table.sv
$REPO_ROOT/rtl/amba/shared/axi_stress_txn_gen.sv
$REPO_ROOT/rtl/amba/shared/axi_stress_mst_rd.sv
$REPO_ROOT/rtl/amba/shared/axi_stress_mst_wr.sv
$REPO_ROOT/rtl/amba/shared/axi_stress_slv_rd.sv
$REPO_ROOT/rtl/amba/shared/axi_stress_slv_wr.sv
