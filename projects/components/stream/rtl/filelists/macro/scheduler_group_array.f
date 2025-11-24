# Filelist for scheduler_group_array module
# Location: projects/components/stream/rtl/filelists/macro/scheduler_group_array.f
#
# Purpose: STREAM Scheduler Group Array - Multi-channel DMA with shared resources
#
# Architecture: 8 scheduler_group instances with:
# - Shared descriptor AXI master (round-robin arbitration)
# - Shared data read interface (to axi_read_engine)
# - Shared data write interface (to axi_write_engine)
# - Unified MonBus aggregation (9 sources: 8 channels + desc AXI monitor)

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Dependencies - Arbiters (for shared descriptor AXI master access)
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv

# Dependencies - AMBA Monitors (for descriptor AXI master monitoring)
# Use -f to include complete monitor infrastructure
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_mon.f

# Dependencies - MonBus Infrastructure (for aggregating 9 MonBus sources)
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv

# Include macro-level component via -f (automatically pulls in FUB dependencies)
-f $STREAM_ROOT/rtl/filelists/macro/scheduler_group.f

# Macro Component - This module
$STREAM_ROOT/rtl/macro/scheduler_group_array.sv
