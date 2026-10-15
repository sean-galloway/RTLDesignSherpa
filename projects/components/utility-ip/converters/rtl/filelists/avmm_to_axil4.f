# Filelist for avmm_to_axil4
# Location: projects/components/utility-ip/converters/rtl/filelists/avmm_to_axil4.f
# Purpose: Avalon-MM slave -> AXI4-Lite master (Intel JTAG-to-Avalon host front-end)

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_master_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_master_rd.f
$CONVERTERS_ROOT/rtl/avmm_to_axil4.sv
