# Filelist for jet_prime_pair_fabric
# Location: projects/components/cache-ip/jet-prime-mesi-l1/rtl/filelists/jet_prime_pair_fabric.f
#
# The pipelined 2-master snoopy manager of the plain-AXI4 jet-prime pair rig
# (DECISION D-8 consumer; jet-prime TASK-001 step 3). Self-contained RTL:
# no foreign module deps, only the shared package and the reset macros.

# Reset macros
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared cache-ip package (l1_pkg: geometry + ACE request classes)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# The fabric
$JET_PRIME_ROOT/rtl/top/jet_prime_pair_fabric.sv
