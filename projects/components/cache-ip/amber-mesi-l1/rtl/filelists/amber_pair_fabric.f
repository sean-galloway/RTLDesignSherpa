# Filelist for amber_pair_fabric
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_pair_fabric.f
#
# The minimal 2-master snoopy manager for the plain-AXI4 pair rig
# (DECISION D-8 consumer). Deps: the shared amber package and rtl/common's
# arbiter_round_robin.

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# The write-port arbiter (amber BUG-005)
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f

# The fabric
$AMBER_ROOT/rtl/top/amber_pair_fabric.sv
