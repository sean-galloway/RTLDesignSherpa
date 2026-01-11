# RAPIDS Beats Scheduler Group Macro File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/scheduler_group_beats.f
# Purpose: Beats Scheduler Group (integrates scheduler + descriptor_engine)

# Include FUB-level file lists (automatically pulls in packages and dependencies)
# Beats-specific FUBs (STREAM-based scheduler and descriptor engine)
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/scheduler_beats.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/descriptor_engine_beats.f

# Additional components used by beats_scheduler_group
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv

# Common utilities
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/scheduler_group_beats.sv
