# Filelist for beats_drain_ctrl module (Beats-specific)
# Location: projects/components/dmas/rapids/rtl/filelists/fub_beats/drain_ctrl_beats.f
# Purpose: Drain control (Virtual FIFO for data availability tracking)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f

# Beats drain control module
$REPO_ROOT/projects/components/dmas/rapids/rtl/fub_beats/drain_ctrl_beats.sv
