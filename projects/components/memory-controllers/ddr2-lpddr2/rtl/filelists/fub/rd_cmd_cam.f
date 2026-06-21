# Filelist for rd_cmd_cam
# Location: projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/fub/rd_cmd_cam.f

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes/ddr2_lpddr2_pkg.sv

# DUT
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/rd_cmd_cam.sv
