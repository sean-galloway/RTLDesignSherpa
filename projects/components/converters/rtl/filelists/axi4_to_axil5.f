# Filelist for axi4_to_axil5
# Location: projects/components/converters/rtl/filelists/axi4_to_axil5.f
# Purpose: AXI4 to AXI5-Lite converter (rd+wr)

# Sub-blocks (consumers -f this file rather than hand-listing them)
-f $CONVERTERS_ROOT/rtl/filelists/axi4_to_axil5_rd.f
-f $CONVERTERS_ROOT/rtl/filelists/axi4_to_axil5_wr.f

$CONVERTERS_ROOT/rtl/axi4_to_axil5.sv
