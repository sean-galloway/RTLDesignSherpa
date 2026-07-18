# Filelist for pumice_wr_intake
# Dumb AXI4 write intake: axi4_slave_wr + AW-meta FIFO + wr-data FIFO + addr_mapper.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv

# AMBA / common deps
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv

# Address decoder
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/addr_mapper.sv

# This FUB
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_wr_intake.sv
