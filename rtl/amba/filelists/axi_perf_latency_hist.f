# Filelist for axi_perf_latency_hist (RFC perfmon Stage D latency histogram).
# Self-contained: only depends on the reset_defs.svh macro header.

+incdir+$REPO_ROOT/rtl/amba/includes

# Header with reset macros (compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

# DUT
$REPO_ROOT/rtl/amba/shared/axi_perf_latency_hist.sv
