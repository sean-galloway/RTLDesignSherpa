# Filelist for sdpram_slave_axil_axi4
# Location: rtl/amba/filelists/sdpram_slave_axil_axi4.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.
#
# sdpram_slave_axil_axi4 = sdpram_core wrapped with an AXIL4 write slave
# surface (axil4_slave_wr) and an AXI4 read slave surface (axi4_slave_rd).

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f

$REPO_ROOT/rtl/amba/shared/sdpram_slave_axil_axi4.sv
