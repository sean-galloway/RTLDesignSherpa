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

# Dependencies - Common utilities
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# Dependencies - Arbiters (for shared resource access)
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv

# Dependencies - GAXI FIFO (used by descriptor engine and monitors)
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# Dependencies - AMBA Monitors
$REPO_ROOT/rtl/amba/shared/axi_monitor_base.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon.sv

# Dependencies - MonBus Infrastructure
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv

# FUB Components - Descriptor Engine
$STREAM_ROOT/rtl/fub/descriptor_engine.sv

# FUB Components - Scheduler
$STREAM_ROOT/rtl/fub/scheduler.sv

# Macro Component - Scheduler Group (instantiated 8 times)
$STREAM_ROOT/rtl/macro/scheduler_group.sv

# Macro Component - This module
$STREAM_ROOT/rtl/macro/scheduler_group_array.sv
