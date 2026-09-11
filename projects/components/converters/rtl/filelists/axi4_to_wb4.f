# Filelist for axi4_to_wb4
# Location: projects/components/converters/rtl/filelists/axi4_to_wb4.f
#
# Complete compile closure: the two AXI4 -> AXI4-Lite decomposers, the
# AXI4-Lite -> Wishbone converter (which brings the rtl/amba wb4 family
# through its own filelist), and this composition wrapper.

-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil4_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil4_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil4_to_wb4.f

$CONVERTERS_ROOT/rtl/axi4_to_wb4.sv
