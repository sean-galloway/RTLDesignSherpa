# Filelist for axi_frontend_macro
# Location: projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/axi_frontend_macro.f
#
# Bundles the AXI-frontend FUBs: addr_mapper (x2 via macro), wr_cmd_cam,
# rd_cmd_cam, wr2rd_forward.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Package files
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes/ddr2_lpddr2_pkg.sv

# FUBs
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/addr_mapper_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/wr_cmd_cam_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/rd_cmd_cam_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/wr2rd_forward_fub.sv

# Macro
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/axi_frontend_macro.sv
