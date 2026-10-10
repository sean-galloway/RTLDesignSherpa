# Filelist for addr_mapper
# Location: projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2/rtl/filelists/fub/addr_mapper.f
#
# Combinational flat-AXI-address → (rank, bank, row, col) decoder.

# Include directories
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Packages
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv

# This FUB
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2/rtl/fub/addr_mapper.sv
