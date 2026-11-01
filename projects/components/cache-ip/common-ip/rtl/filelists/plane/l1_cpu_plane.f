# Filelist for l1_cpu_plane
# Location: projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_cpu_plane.f
#
# CPU plane for the cache-ip shared MESI L1: the GAXI CPU slave frontend
# isolated as a protocol-generation boundary. This list depends only on
# the frontend and the shared package.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# CPU-facing GAXI slave
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_frontend.f

# The CPU plane
$CACHE_COMMON_ROOT/rtl/plane/l1_cpu_plane.sv
