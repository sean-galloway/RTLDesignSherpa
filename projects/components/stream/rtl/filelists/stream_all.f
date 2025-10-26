# STREAM Master Filelist
# Location: projects/components/stream/rtl/filelists/stream_all.f
# Purpose: Complete STREAM component for linting (all FUB and macro modules)

# Include directories
+incdir+$REPO_ROOT/projects/components/stream/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/stream/rtl/includes/stream_pkg.sv

# Common dependencies (order matters - dependencies first)
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# AMBA monitoring infrastructure (used by macro modules)
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon.sv
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv

# STREAM FUB modules
$REPO_ROOT/projects/components/stream/rtl/stream_fub/simple_sram.sv
$REPO_ROOT/projects/components/stream/rtl/stream_fub/descriptor_engine.sv
$REPO_ROOT/projects/components/stream/rtl/stream_fub/axi_read_engine.sv
$REPO_ROOT/projects/components/stream/rtl/stream_fub/axi_write_engine.sv
$REPO_ROOT/projects/components/stream/rtl/stream_fub/scheduler.sv
$REPO_ROOT/projects/components/stream/rtl/stream_fub/sram_controller.sv
$REPO_ROOT/projects/components/stream/rtl/stream_fub/perf_profiler.sv

# STREAM macro modules
$REPO_ROOT/projects/components/stream/rtl/stream_macro/scheduler_group.sv
$REPO_ROOT/projects/components/stream/rtl/stream_macro/datapath.sv
$REPO_ROOT/projects/components/stream/rtl/stream_macro/scheduler_group_array.sv
$REPO_ROOT/projects/components/stream/rtl/stream_macro/monbus_axil_group.sv
$REPO_ROOT/projects/components/stream/rtl/stream_macro/apbtodescr.sv
