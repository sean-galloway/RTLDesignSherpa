# Filelist for axil5_master_rd
# Location: rtl/amba/filelists/axil5_master_rd.f
#
# AXI5-Lite transport. Same dependency set as the AXI4-Lite module it mirrors:
# the optional signal groups ride in the SKID payload, so they add no modules.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/axil5/axil5_master_rd.sv
