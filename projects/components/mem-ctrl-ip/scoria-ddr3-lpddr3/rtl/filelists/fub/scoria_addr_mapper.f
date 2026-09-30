# Filelist for scoria_addr_mapper
# Location: projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/addr_mapper.f
#
# Combinational flat-AXI-address → (rank, bank, row, col) decoder.

# Include directories
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Packages
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/includes/scoria_pkg.sv

# This FUB
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_addr_mapper.sv
