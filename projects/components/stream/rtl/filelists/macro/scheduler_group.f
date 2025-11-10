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

# Dependencies - Common utilities
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# Dependencies - GAXI FIFO (used by descriptor engine)
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# FUB Components - Descriptor Engine
$STREAM_ROOT/rtl/fub/descriptor_engine.sv

# FUB Components - Scheduler
$STREAM_ROOT/rtl/fub/scheduler.sv

# Macro Component - This module
$STREAM_ROOT/rtl/macro/scheduler_group.sv
