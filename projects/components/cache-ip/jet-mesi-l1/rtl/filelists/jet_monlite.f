# Filelist for jet_monlite
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_monlite.f
#
# The J7 MonBus observer for the jet MESI L1.  Self-contained: pulls the
# packages it needs and the house shared-storage FIFO primitive.  No
# common-ip source is modified.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Packages (l1_pkg first; jet_pkg closes it)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f
-f $JET_ROOT/rtl/filelists/jet_pkg.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

# Shared storage primitive used by the output queue
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

# The J7 observer itself
$JET_ROOT/rtl/fub/jet_monlite.sv
