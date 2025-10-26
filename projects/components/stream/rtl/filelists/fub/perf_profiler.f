# Filelist for perf_profiler module
# Location: projects/components/stream/rtl/filelists/fub/perf_profiler.f

# Include directories
+incdir+$REPO_ROOT/projects/components/stream/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# GAXI FIFO dependencies (order matters - dependencies first)
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# Performance profiler module
$REPO_ROOT/projects/components/stream/rtl/stream_fub/perf_profiler.sv
