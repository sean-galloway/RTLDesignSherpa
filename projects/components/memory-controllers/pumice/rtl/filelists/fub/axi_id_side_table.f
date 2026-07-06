# Filelist for axi_id_side_table
# Location: projects/components/memory-controllers/pumice/rtl/filelists/fub/axi_id_side_table.f
#
# Per-AXI-ID metadata side-table — captures AW/AR attributes at host
# handshake and replays user / qos at completion + scheduling time.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
$REPO_ROOT/projects/components/memory-controllers/pumice/rtl/includes/pumice_pkg.sv

# This FUB
$REPO_ROOT/projects/components/memory-controllers/pumice/rtl/fub/axi_id_side_table.sv
