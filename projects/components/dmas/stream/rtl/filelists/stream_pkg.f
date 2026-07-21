# Filelist for stream_pkg
# Location: projects/components/dmas/stream/rtl/filelists/stream_pkg.f
# Purpose: STREAM package only, for cross-component consumers.
#
# RAPIDS reuses several STREAM sources and needs stream_pkg in scope. It should
# -f this file rather than naming stream_pkg.sv directly, so STREAM keeps
# ownership of its own package's dependencies.

+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

$STREAM_ROOT/rtl/includes/stream_pkg.sv
