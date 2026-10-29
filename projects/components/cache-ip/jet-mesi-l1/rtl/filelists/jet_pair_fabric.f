# Filelist for jet_pair_fabric
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_pair_fabric.f
#
# The minimal 2-master snoopy manager for the plain-AXI4 jet pair rig
# (DECISION D-8 consumer; the spec's "amber_pair_fabric hosts two jets"
# deliverable, jet-named). Self-contained RTL: no foreign module deps,
# only the shared package.

# Shared cache-ip package (l1_pkg: geometry + ACE request classes)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# The fabric
$JET_ROOT/rtl/top/jet_pair_fabric.sv
