# Filelist for latency_bridge test

# Include directories
+incdir+${REPO_ROOT}/rtl/amba/includes
+incdir+${REPO_ROOT}/projects/components/dma-ip/rapids/rtl/includes

# Package files
${REPO_ROOT}/rtl/amba/includes/reset_defs.svh
${REPO_ROOT}/rtl/amba/includes/fifo_defs.svh

# Dependencies (for gaxi_fifo_sync)
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

# DUT
${REPO_ROOT}/projects/components/dma-ip/rapids/rtl/fub/latency_bridge.sv
