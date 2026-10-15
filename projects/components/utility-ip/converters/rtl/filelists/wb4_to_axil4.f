# Filelist for wb4_to_axil4
# Location: projects/components/utility-ip/converters/rtl/filelists/wb4_to_axil4.f
# Purpose: Wishbone B4 slave -> AXI4-Lite master (slave + core + axil masters)

+incdir+$REPO_ROOT/rtl/amba/includes

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

-f $REPO_ROOT/rtl/amba/filelists/wb4_slave.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_master_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_master_rd.f
-f $CONVERTERS_ROOT/rtl/filelists/wb4_to_axil4_core.f
$CONVERTERS_ROOT/rtl/wb4_to_axil4.sv
