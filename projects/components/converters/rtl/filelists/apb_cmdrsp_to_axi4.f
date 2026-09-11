# Filelist for apb_cmdrsp_to_axi4
# Location: projects/components/converters/rtl/filelists/apb_cmdrsp_to_axi4.f
# Purpose: APB cmd/rsp stream -> single-beat AXI4 requester (the requester
#          half of apb4_to_axi4 / apb5_to_axi4)

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$CONVERTERS_ROOT/rtl/apb_cmdrsp_to_axi4.sv
