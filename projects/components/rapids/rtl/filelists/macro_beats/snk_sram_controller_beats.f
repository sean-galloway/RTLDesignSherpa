# RAPIDS Sink SRAM Controller Macro File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/snk_sram_controller_beats.f
# Purpose: Multi-channel Sink SRAM Controller (Network Slave -> SRAM -> AXI Write Engine)

# Include FUB-level dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/alloc_ctrl_beats.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/drain_ctrl_beats.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/latency_bridge_beats.f

# Common FIFO dependencies
$REPO_ROOT/rtl/common/fifo_sync.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/counter_bin.sv

# GAXI FIFO (used by controller unit)
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# Includes
+incdir+$REPO_ROOT/rtl/common/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Per-channel unit module
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/snk_sram_controller_unit_beats.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/snk_sram_controller_beats.sv
