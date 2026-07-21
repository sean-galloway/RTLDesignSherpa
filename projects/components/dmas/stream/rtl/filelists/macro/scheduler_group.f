# Filelist for scheduler_group module
# Location: projects/components/dmas/stream/rtl/filelists/macro/scheduler_group.f
#
# Purpose: STREAM Scheduler Group - Wrapper combining scheduler + descriptor engine
#
# Architecture: Single channel combining:
# - descriptor_engine (fetches descriptors from memory via AXI)
# - scheduler (controls data transfers)
# - MonBus aggregation from 2 sources

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Include FUB-level components via -f (automatically pulls in dependencies)
-f $STREAM_ROOT/rtl/filelists/fub/descriptor_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/scheduler.f

# Macro Component - This module
$STREAM_ROOT/rtl/macro/scheduler_group.sv
