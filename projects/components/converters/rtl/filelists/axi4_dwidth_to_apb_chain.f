# Filelist for axi4_dwidth_to_apb_chain FUB-level chain
# Location: projects/components/converters/rtl/filelists/axi4_dwidth_to_apb_chain.f
# Purpose: Chain wrapper: axi4_dwidth_converter_rd → axi4_to_apb_shim.
#          Exists to surface the bridge's 1x5_rd_boundary_probe hang
#          at the FUB level (same chain the bridge instantiates between
#          a wide master and a narrow APB peripheral).

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies — CDC and synchronization (used by APB shim)
$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv
$REPO_ROOT/rtl/amba/shared/cdc_4_phase_handshake.sv

# Dependencies — GAXI infrastructure
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# Dependencies — APB infrastructure
$REPO_ROOT/rtl/amba/apb/apb_master.sv
$REPO_ROOT/rtl/amba/apb/apb_master_stub.sv

# Dependencies — Common modules
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# Dependencies — AXI address generation
$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv

# Dependencies — AXI4 slave stubs (used by APB shim)
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_wr_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_rd_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_stub.sv

# Dependencies — AXI4 → APB converter core
$CONVERTERS_ROOT/rtl/axi4_to_apb_convert.sv

# Dependencies — validated data-sizing primitives (rd uses both:
# UPSIZE direction → axi_data_dnsize; DOWNSIZE direction → axi_data_upsize)
$CONVERTERS_ROOT/rtl/axi_data_upsize.sv
$CONVERTERS_ROOT/rtl/axi_data_dnsize.sv

# Stage 1: AXI4 read data width converter (wide → narrow on R)
$CONVERTERS_ROOT/rtl/axi4_dwidth_converter_rd.sv

# Stage 2: AXI4 → APB shim
$CONVERTERS_ROOT/rtl/axi4_to_apb_shim.sv

# Top: the chain wrapper
$CONVERTERS_ROOT/rtl/axi4_dwidth_to_apb_chain.sv
