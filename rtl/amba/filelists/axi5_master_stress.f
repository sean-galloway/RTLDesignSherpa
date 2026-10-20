# Filelist for axi5_master_stress (AXI5 bus-stress master)
# Location: rtl/amba/filelists/axi5_master_stress.f

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axi_stress_core.f
-f $REPO_ROOT/rtl/amba/filelists/axi5_master_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi5_master_wr.f
$REPO_ROOT/rtl/amba/shared/axi5_master_stress.sv
