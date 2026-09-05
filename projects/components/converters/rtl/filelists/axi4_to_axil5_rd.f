# Filelist for axi4_to_axil5_rd
# Location: projects/components/converters/rtl/filelists/axi4_to_axil5_rd.f
#
# The AXI5-Lite read converter is a sideband wrapper over
# axi4_to_axil4_rd, so its closure is that module's closure plus the
# wrapper source.

-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil4_rd.f

$CONVERTERS_ROOT/rtl/axi4_to_axil5_rd.sv
