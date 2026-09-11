# Filelist for apb5_to_axi4
# Location: projects/components/converters/rtl/filelists/apb5_to_axi4.f
#
# Complete compile closure: the APB5 completer front end (rtl/amba, via its
# own filelist), the cmd/rsp -> AXI4 requester, and this wrapper.

-f $REPO_ROOT/rtl/amba/filelists/apb5_slave.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/apb_cmdrsp_to_axi4.f

$CONVERTERS_ROOT/rtl/apb5_to_axi4.sv
