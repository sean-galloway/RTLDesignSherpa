# Filelist for wb4_to_axi4
# Location: projects/components/utility-ip/converters/rtl/filelists/wb4_to_axi4.f
#
# Complete compile closure: wb4_to_axil4's own closure (wb4_slave, the
# in-order core, the axil4 masters) plus this AXI4 promotion wrapper.

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/wb4_to_axil4.f

$CONVERTERS_ROOT/rtl/wb4_to_axi4.sv
