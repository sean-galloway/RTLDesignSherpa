# Filelist for scheduler_group_array module
# Location: projects/components/dmas/stream/rtl/filelists/macro/scheduler_group_array.f
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

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_single_client.f

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Dependencies - AMBA Monitors (for descriptor AXI master monitoring)
# Use -f to include complete monitor infrastructure
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_mon.f

# Include macro-level component via -f (automatically pulls in FUB dependencies)
-f $STREAM_ROOT/rtl/filelists/macro/scheduler_group.f

# Macro Component - This module
$STREAM_ROOT/rtl/macro/scheduler_group_array.sv
