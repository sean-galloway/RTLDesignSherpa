# Filelist for addr_mapper
# Location: projects/components/memory-controllers/pumice/rtl/filelists/fub/addr_mapper.f
#
# Combinational flat-AXI-address → (rank, bank, row, col) decoder.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Packages
$REPO_ROOT/projects/components/memory-controllers/pumice/rtl/includes/pumice_pkg.sv

# This FUB
$REPO_ROOT/projects/components/memory-controllers/pumice/rtl/fub/addr_mapper.sv
