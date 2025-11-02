# Filelist for apbtodescr module (APB-to-Descriptor Router)
# Location: projects/components/stream/rtl/filelists/macro/apbtodescr.f

# Include directories
+incdir+$REPO_ROOT/projects/components/stream/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Package files (MUST be first)
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/stream/rtl/includes/stream_pkg.sv

# APB to descriptor module
$REPO_ROOT/projects/components/stream/rtl/stream_macro/apbtodescr.sv
