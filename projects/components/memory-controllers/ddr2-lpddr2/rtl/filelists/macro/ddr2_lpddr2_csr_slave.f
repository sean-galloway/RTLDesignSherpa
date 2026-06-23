# Filelist for ddr2_lpddr2_csr_slave (CSR slave macro)
# Bundles: apb_slave_cdc + peakrdl_to_cmdrsp + PeakRDL regblock
# + config_block projection.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/regs/generated/rtl
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# AMBA APB infrastructure
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/shared/cdc_synchronizer.sv
$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv
$REPO_ROOT/rtl/amba/shared/cdc_4_phase_handshake.sv
$REPO_ROOT/rtl/amba/shared/cdc_open_loop.sv
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc.sv

# CMD/RSP → PeakRDL passthrough adapter
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

# PeakRDL-generated register block
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/regs/generated/rtl/ddr2_lpddr2_csr_pkg.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/regs/generated/rtl/ddr2_lpddr2_csr.sv

# Config-block projection
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/ddr2_lpddr2_config_block.sv

# CSR slave macro
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/ddr2_lpddr2_csr_slave.sv
