# Filelist for l1_core
# Location: projects/components/cache-ip/common-ip/rtl/filelists/l1_core.f
#
# Aggregate CPU plane + coherence-core plane for the cache-ip shared MESI
# L1. The ACE snoop responder moved to the fabric plane in Task 1; this
# list closes the two planes and the aggregate top.

# CPU plane (l1_cpu_frontend)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_cpu_plane.f

# Coherence-core plane (l1_control, arrays, repl, fill/drain, monlite)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_coh_core.f

# Aggregate top
$CACHE_COMMON_ROOT/rtl/top/l1_core.sv
