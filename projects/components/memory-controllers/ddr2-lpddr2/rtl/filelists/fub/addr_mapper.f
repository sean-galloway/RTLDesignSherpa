# Filelist for addr_mapper
# Location: projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/fub/addr_mapper.f
#
# Combinational flat-AXI-address → (rank, bank, row, col) decoder.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Packages
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes/ddr2_lpddr2_pkg.sv

# This FUB
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/addr_mapper.sv
