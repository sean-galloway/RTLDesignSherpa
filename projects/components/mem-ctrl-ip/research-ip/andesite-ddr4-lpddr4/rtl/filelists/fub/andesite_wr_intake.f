# Filelist for andesite_wr_intake
# Dumb AXI4 write intake: axi4_slave_wr + AW-meta FIFO + wr-data FIFO + addr_mapper.

# Include directories
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/includes/andesite_pkg.sv

# AMBA / common deps
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f

# Address decoder
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_addr_mapper.sv

# This FUB
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_wr_intake.sv
