# Filelist for datapath_rd_test module (with 8 scheduler instances)
# Location: projects/components/stream/rtl/filelists/macro/datapath_rd_test.f
#
# Architecture: Uses 8 real scheduler modules (not scheduler_group)
# - Descriptors fed directly from testbench (simple valid/ready/packet interface)
# - All schedulers feed into shared axi_read_engine via arbiter
# - Descriptor interfaces exposed as descriptor_0..7 for GAXI master drivers

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Dependencies - Arbiter (for axi_read_engine scheduler arbitration)
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv

# Dependencies - GAXI FIFO, simple SRAM, counter_bin, fifo_control
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv


# FUB Components - Scheduler (parses descriptors, drives read engine)
$STREAM_ROOT/rtl/fub/scheduler.sv

# Component modules - AXI Read Engine and supporting logic
$STREAM_ROOT/rtl/fub/stream_alloc_ctrl.sv
$STREAM_ROOT/rtl/fub/stream_drain_ctrl.sv
$STREAM_ROOT/rtl/fub/stream_latency_bridge.sv
$STREAM_ROOT/rtl/fub/axi_read_engine.sv
$STREAM_ROOT/rtl/fub/sram_controller_unit.sv
$STREAM_ROOT/rtl/fub/sram_controller.sv

# Test wrapper module (instantiates 8 scheduler + axi_read_engine)
$STREAM_ROOT/rtl/macro/datapath_rd_test.sv
