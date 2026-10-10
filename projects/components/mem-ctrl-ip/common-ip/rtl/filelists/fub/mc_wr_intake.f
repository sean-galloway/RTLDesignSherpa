# Filelist for mc_wr_intake (common-ip; extracted from pumice Phase 2 Task 2)
# Dumb AXI4 write intake: axi4_slave_wr + AW-meta FIFO + wr-data FIFO + addr_mapper.

# Include directories
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f

# AMBA / common deps
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f

# Address decoder
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_addr_mapper.f

# This FUB
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_wr_intake.sv
