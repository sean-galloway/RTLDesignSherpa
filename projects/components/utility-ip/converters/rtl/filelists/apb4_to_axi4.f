# Filelist for apb4_to_axi4
# Location: projects/components/utility-ip/converters/rtl/filelists/apb4_to_axi4.f
#
# Complete compile closure: the APB4 completer front end (owned by
# rtl/amba, pulled in by its own filelist -- never hand-list its sources
# here), the cmd/rsp -> AXI4 requester, and this wrapper.

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/apb_cmdrsp_to_axi4.f

$CONVERTERS_ROOT/rtl/apb4_to_axi4.sv
