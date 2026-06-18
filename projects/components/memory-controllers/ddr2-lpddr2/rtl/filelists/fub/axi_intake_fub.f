# Filelist for axi_intake_fub
# Location: projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/fub/axi_intake_fub.f
#
# Slave-side AXI4 protocol intake, built on rtl/amba axi4_slave_wr / axi4_slave_rd
# plus gaxi_fifo_sync for AW/AR pending and B response FIFOs.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes/ddr2_lpddr2_pkg.sv

# AMBA AXI4 slave-side protocol modules (instantiated by axi_intake_fub)
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv

# This FUB
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/axi_intake_fub.sv
