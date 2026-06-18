# Filelist for axi_frontend_macro
# Location: projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/axi_frontend_macro.f
#
# Bundles axi_intake_fub + 2x addr_mapper_fub + wr_cmd_cam + rd_cmd_cam +
# wr2rd_forward into one synthesizable / testable group with raw AXI4 host
# ports at the boundary.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes/ddr2_lpddr2_pkg.sv

# AMBA building blocks (consumed by axi_intake_fub via axi4_slave_wr/rd
# and gaxi_fifo_sync; consumed by gaxi_fifo_sync via counter_bin +
# fifo_control)
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv

# FUBs
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/addr_mapper_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/wr_cmd_cam_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/rd_cmd_cam_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/wr2rd_forward_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/axi_intake_fub.sv

# Macro
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/axi_frontend_macro.sv
