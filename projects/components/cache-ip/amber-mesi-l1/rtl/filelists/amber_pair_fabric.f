# Filelist for amber_pair_fabric
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_pair_fabric.f
#
# The minimal 2-master snoopy manager for the plain-AXI4 pair rig
# (DECISION D-8 consumer). Self-contained RTL: no foreign module deps, only
# the shared amber package.

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# The fabric
$AMBER_ROOT/rtl/top/amber_pair_fabric.sv
