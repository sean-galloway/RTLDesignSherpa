# Filelist for datapath_wr_test module (with 8 scheduler instances)
# Location: projects/components/dmas/stream/rtl/filelists/macro/datapath_wr_test.f
#
# Architecture: Uses 8 real scheduler modules (not scheduler_group)
# - Descriptors fed directly from testbench (simple valid/ready/packet interface)
# - All schedulers feed into shared axi_write_engine via arbiter
# - Descriptor interfaces exposed as descriptor_0..7 for GAXI master drivers

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

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Include FUB-level components via -f (automatically pulls in dependencies)
-f $STREAM_ROOT/rtl/filelists/fub/scheduler.f
-f $STREAM_ROOT/rtl/filelists/fub/axi_write_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/sram_controller.f

# Test wrapper module (instantiates 8 scheduler + axi_write_engine)
$STREAM_ROOT/rtl/macro/datapath_wr_test.sv
