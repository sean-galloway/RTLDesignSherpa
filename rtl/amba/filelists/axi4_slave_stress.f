# Filelist for axi4_slave_stress (AXI4 bus-stress slave)
# Location: rtl/amba/filelists/axi4_slave_stress.f

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axi_stress_core.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
$REPO_ROOT/rtl/amba/shared/axi4_slave_stress.sv
