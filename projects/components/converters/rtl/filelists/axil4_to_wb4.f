# Filelist for axil4_to_wb4
# Location: projects/components/converters/rtl/filelists/axil4_to_wb4.f
# Purpose: AXI4-Lite slave -> Wishbone B4 master (skids + core + wb4_master)

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/wb4_master.f
-f $CONVERTERS_ROOT/rtl/filelists/axil4_to_wb4_core.f
$CONVERTERS_ROOT/rtl/axil4_to_wb4.sv
