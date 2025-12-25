# Filelist for apbtodescr module (APB-to-Descriptor Router)
# Location: projects/components/stream/rtl/filelists/fub/apbtodescr.f

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Package files (MUST be first)
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# APB to descriptor module
$STREAM_ROOT/rtl/fub/apbtodescr.sv
