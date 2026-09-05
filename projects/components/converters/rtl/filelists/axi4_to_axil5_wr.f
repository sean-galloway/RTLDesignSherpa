# Filelist for axi4_to_axil5_wr
# Location: projects/components/converters/rtl/filelists/axi4_to_axil5_wr.f
#
# The AXI5-Lite write converter is a sideband wrapper over
# axi4_to_axil4_wr, so its closure is that module's closure plus the
# wrapper source.

-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil4_wr.f

$CONVERTERS_ROOT/rtl/axi4_to_axil5_wr.sv
