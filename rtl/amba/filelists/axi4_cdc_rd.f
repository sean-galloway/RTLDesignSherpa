# Filelist for axi4_cdc_rd
# Location: rtl/amba/filelists/axi4_cdc_rd.f
# Purpose: AXI4 read (AR, R) channels across a clock-domain boundary,
#          one gaxi_fifo_async per channel (BRIDGE-017 CDC slave ports).

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
$REPO_ROOT/rtl/amba/axi4/axi4_cdc_rd.sv
