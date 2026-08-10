# Filelist for axi4_to_apb5_shim
# Location: projects/components/converters/rtl/filelists/axi4_to_apb5_shim.f
#
# Declares the complete compile closure: the APB5 shim is a sideband
# wrapper over axi4_to_apb4_shim, so its closure is that shim's closure
# plus the wrapper source.

-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_apb4_shim.f

$CONVERTERS_ROOT/rtl/axi4_to_apb5_shim.sv
