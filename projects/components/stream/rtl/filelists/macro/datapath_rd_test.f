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
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Include FUB-level components via -f (automatically pulls in dependencies)
-f $STREAM_ROOT/rtl/filelists/fub/scheduler.f
-f $STREAM_ROOT/rtl/filelists/fub/axi_read_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/sram_controller.f

# Test wrapper module (instantiates 8 scheduler + axi_read_engine)
$STREAM_ROOT/rtl/macro/datapath_rd_test.sv
