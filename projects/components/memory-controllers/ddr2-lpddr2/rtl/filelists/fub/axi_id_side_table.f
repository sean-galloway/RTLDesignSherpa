# Filelist for axi_id_side_table
# Location: projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/fub/axi_id_side_table.f
#
# Per-AXI-ID metadata side-table — captures AW/AR attributes at host
# handshake and replays user / qos at completion + scheduling time.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes/ddr2_lpddr2_pkg.sv

# This FUB
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/axi_id_side_table.sv
