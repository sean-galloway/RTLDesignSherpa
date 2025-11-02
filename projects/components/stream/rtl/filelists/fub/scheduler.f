# Filelist for scheduler module
# Location: projects/components/stream/rtl/filelists/fub/scheduler.f

# Include directories
+incdir+$REPO_ROOT/projects/components/stream/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/stream/rtl/includes/stream_pkg.sv

# Scheduler module
$REPO_ROOT/projects/components/stream/rtl/stream_fub/scheduler.sv
