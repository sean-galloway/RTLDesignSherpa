# Filelist for axi4_to_apb5_shim
# Location: projects/components/utility-ip/converters/rtl/filelists/axi4_to_apb5_shim.f
#
# Declares the complete compile closure: the APB5 shim is a sideband
# wrapper over axi4_to_apb4_shim, so its closure is that shim's closure
# plus the wrapper source.

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_to_apb4_shim.f

$CONVERTERS_ROOT/rtl/axi4_to_apb5_shim.sv
