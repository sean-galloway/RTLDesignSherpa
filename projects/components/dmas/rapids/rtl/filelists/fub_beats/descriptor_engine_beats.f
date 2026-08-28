# RAPIDS Descriptor Engine FUB File List (Beats-specific)
# Location: projects/components/dmas/rapids/rtl/filelists/fub_beats/descriptor_engine_beats.f
# Purpose: Descriptor Engine module and its direct dependencies (STREAM-based, beats mode)

# Include directories
+incdir+$REPO_ROOT/projects/components/dmas/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Package files (MUST be first, in dependency order)
# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/common/filelists/fifo_sync.f

$REPO_ROOT/projects/components/dmas/rapids/rtl/includes/rapids_pkg.sv

# DUT module
$REPO_ROOT/projects/components/dmas/rapids/rtl/fub_beats/descriptor_engine_beats.sv
