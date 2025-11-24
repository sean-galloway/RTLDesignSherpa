# Filelist for scheduler_group module
# Location: projects/components/stream/rtl/filelists/macro/scheduler_group.f
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

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Include FUB-level components via -f (automatically pulls in dependencies)
-f $STREAM_ROOT/rtl/filelists/fub/descriptor_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/scheduler.f

# Macro Component - This module
$STREAM_ROOT/rtl/macro/scheduler_group.sv
