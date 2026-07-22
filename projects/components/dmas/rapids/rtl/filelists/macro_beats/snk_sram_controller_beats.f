# RAPIDS Sink SRAM Controller Macro File List
# Location: projects/components/dmas/rapids/rtl/filelists/macro_beats/snk_sram_controller_beats.f
# Purpose: Multi-channel Sink SRAM Controller (Network Slave -> SRAM -> AXI Write Engine)

# Include FUB-level dependencies
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/alloc_ctrl_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/drain_ctrl_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/latency_bridge_beats.f

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/common/filelists/fifo_sync.f

# Includes
+incdir+$REPO_ROOT/rtl/common/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Per-channel unit module
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/snk_sram_controller_unit_beats.sv

# DUT module
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/snk_sram_controller_beats.sv
