# Filelist for andesite_addr_mapper
# Location: projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/filelists/fub/addr_mapper.f
#
# Combinational flat-AXI-address → (rank, bank, row, col) decoder.

# Include directories
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Packages
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/includes/andesite_pkg.sv

# This FUB
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_addr_mapper.sv
