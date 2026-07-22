# RAPIDS Beats Scheduler Group Macro File List
# Location: projects/components/dmas/rapids/rtl/filelists/macro_beats/scheduler_group_beats.f
# Purpose: Beats Scheduler Group (integrates scheduler + descriptor_engine)

# Include FUB-level file lists (automatically pulls in packages and dependencies)
# Beats-specific FUBs (STREAM-based scheduler and descriptor engine)
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/scheduler_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/descriptor_engine_beats.f

# Control engines (common, shared with non-beats) - Phase 2 producer/consumer
$REPO_ROOT/projects/components/dmas/rapids/rtl/fub/ctrlrd_engine.sv
$REPO_ROOT/projects/components/dmas/rapids/rtl/fub/ctrlwr_engine.sv

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# DUT module
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/scheduler_group_beats.sv
