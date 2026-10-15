# Filelist for apb_cmdrsp_to_axi4
# Location: projects/components/utility-ip/converters/rtl/filelists/apb_cmdrsp_to_axi4.f
# Purpose: APB cmd/rsp stream -> single-beat AXI4 requester (the requester
#          half of apb4_to_axi4 / apb5_to_axi4)

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$CONVERTERS_ROOT/rtl/apb_cmdrsp_to_axi4.sv
