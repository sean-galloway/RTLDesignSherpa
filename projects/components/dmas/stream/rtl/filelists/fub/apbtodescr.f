# Filelist for apbtodescr module (APB-to-Descriptor Router)
# Location: projects/components/dmas/stream/rtl/filelists/fub/apbtodescr.f

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Package files (MUST be first)
# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

$STREAM_ROOT/rtl/includes/stream_pkg.sv

# APB to descriptor module
$STREAM_ROOT/rtl/fub/apbtodescr.sv
