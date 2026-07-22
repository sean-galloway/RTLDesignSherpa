# Filelist for sdpram_slave_axi4_axi4
# Location: rtl/amba/filelists/sdpram_slave_axi4_axi4.f
#
# sdpram_slave_axi4_axi4 = sdpram_core wrapped with AXI4 write + read slave
# surfaces.  The AXIL4 slave surfaces are compiled in as well: the AXI4/AXIL
# wrappers share the same core, and the AXIL surface is instantiated by the
# sibling sdpram_slave_*_axil wrappers built from this same core.
#
# rtl/common is an include dir (not a source dir) for this wrapper -- the
# original test passed it as an include path.

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common

$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_wr.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv
$REPO_ROOT/rtl/amba/shared/sdpram_core.sv
$REPO_ROOT/rtl/amba/shared/sdpram_slave_axi4_axi4.sv
