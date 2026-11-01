# Filelist for l1_chi_plane_stub
# Location: projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_chi_plane_stub.f
#
# CHI fabric plane stub for the cache-ip shared MESI L1: an elaboration-only
# proof that the core-facing fabric seam is syntactically complete.  The stub
# imports l1_pkg for geometry defaults and AMBER_CRRESP_WIDTH only.

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# The CHI fabric plane stub
$CACHE_COMMON_ROOT/rtl/plane/l1_chi_plane_stub.sv
