# APB Crossbar Common Dependencies File List
# Location: projects/components/apb_xbar/rtl/filelists/core/apb_xbar_common.f
# Purpose: Common dependencies for all APB crossbar variants

# Include directories for SystemVerilog header files
+incdir+$REPO_ROOT/rtl/amba/includes

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/apb_master.f
-f $REPO_ROOT/rtl/amba/filelists/apb_slave.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f
-f $REPO_ROOT/rtl/common/filelists/encoder.f
