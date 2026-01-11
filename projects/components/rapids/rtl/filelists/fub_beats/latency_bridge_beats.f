# Filelist for beats_latency_bridge test

# Include directories
+incdir+${REPO_ROOT}/rtl/amba/includes
+incdir+${REPO_ROOT}/projects/components/rapids/rtl/includes

# Package files
${REPO_ROOT}/rtl/amba/includes/reset_defs.svh
${REPO_ROOT}/rtl/amba/includes/fifo_defs.svh

# Dependencies (for gaxi_fifo_sync)
${REPO_ROOT}/rtl/common/counter_bin.sv
${REPO_ROOT}/rtl/common/fifo_control.sv
${REPO_ROOT}/rtl/amba/gaxi/gaxi_fifo_sync.sv

# DUT
${REPO_ROOT}/projects/components/rapids/rtl/fub_beats/latency_bridge_beats.sv
