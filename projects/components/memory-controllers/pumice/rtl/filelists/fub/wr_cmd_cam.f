# Filelist for wr_cmd_cam
# Location: projects/components/memory-controllers/pumice/rtl/filelists/fub/wr_cmd_cam.f

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
$REPO_ROOT/projects/components/memory-controllers/pumice/rtl/includes/pumice_pkg.sv

# DUT
$REPO_ROOT/projects/components/memory-controllers/pumice/rtl/fub/wr_cmd_cam.sv
