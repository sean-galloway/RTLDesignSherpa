# RAPIDS Scheduler Group Macro File List
# Location: projects/components/rapids/rtl/filelists/macro/scheduler_group.f
# Purpose: Scheduler Group (integrates scheduler, descriptor_engine, program_engine)

# Include FUB-level file lists (automatically pulls in packages and dependencies)
# Beats-specific FUBs (STREAM-based scheduler and descriptor engine)
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/scheduler_beats.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/descriptor_engine_beats.f
# Chunk-based FUBs (original RAPIDS control engines)
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub/ctrlrd_engine.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub/ctrlwr_engine.f

# Additional components used by scheduler_group
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv

# Additional AXI4 components
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv

# Common utilities
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/clock_gate_ctrl.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/macro/scheduler_group.sv
