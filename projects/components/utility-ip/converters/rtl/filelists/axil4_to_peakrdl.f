# Filelist for axil4_to_peakrdl
# Location: projects/components/utility-ip/converters/rtl/filelists/axil4_to_peakrdl.f
#
# AXI4-Lite slave -> PeakRDL passthrough cpuif, same clock. Leaf module on
# reset_defs.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

$CONVERTERS_ROOT/rtl/axil4_to_peakrdl.sv
