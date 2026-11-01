# Filelist for l1_coh_core
# Location: projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_coh_core.f
#
# Coherence-core plane for the cache-ip shared MESI L1: the cache state
# machine, arrays, replacement, fill/drain engines, MonBus observer, and
# the integration logic that binds them. The CPU plane and fabric plane
# are separate named boundaries.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# Leaf arrays + replacement engine
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_tag_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_data_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_repl.f

# Blocking-pipeline control FSM
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_control.f

# Fill / drain sequencing engines
# R-beat staging queue
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

$CACHE_COMMON_ROOT/rtl/fub/l1_fill.sv
$CACHE_COMMON_ROOT/rtl/fub/l1_drain.sv

# Drop-and-count MonBus observer
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_monlite.f

# The coherence core plane
$CACHE_COMMON_ROOT/rtl/plane/l1_coh_core.sv
