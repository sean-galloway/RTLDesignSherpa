# Filelist for axi_write_engine module (Beats-specific)
# Location: projects/components/dmas/rapids/rtl/filelists/fub_beats/axi_write_engine_beats.f
# Purpose: Multi-channel AXI4 write engine with data-aware arbitration (STREAM-based, beats mode)

# Include directories
+incdir+$REPO_ROOT/projects/components/dmas/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f

# Package files (MUST be first, in dependency order)
# Monitor packages - common first, then protocol-specific, then unified
$REPO_ROOT/projects/components/dmas/rapids/rtl/includes/rapids_pkg.sv

# AXI write engine module
$REPO_ROOT/projects/components/dmas/rapids/rtl/fub_beats/axi_write_engine_beats.sv
