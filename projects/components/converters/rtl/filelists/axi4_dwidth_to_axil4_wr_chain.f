# Filelist for axi4_dwidth_to_axil4_wr_chain FUB-level chain
# Location: projects/components/converters/rtl/filelists/axi4_dwidth_to_axil4_wr_chain.f
# Purpose: Chain wrapper: axi4_dwidth_converter_wr → axi4_to_axil4_wr.
#          Exists to surface the b2b page-probe class of bug at the FUB
#          level (same chain the bridge instantiates).

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies — skid buffers used by the dwidth converter
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Dependencies — validated data-sizing primitives (W path)
$CONVERTERS_ROOT/rtl/axi_data_upsize.sv
$CONVERTERS_ROOT/rtl/axi_data_dnsize.sv

# Stage 1: AXI4 width converter (wide → narrow on W)
$CONVERTERS_ROOT/rtl/axi4_dwidth_converter_wr.sv

# Stage 2: AXI4 → AXIL4 burst-decomposition shim
$CONVERTERS_ROOT/rtl/axi4_to_axil4_wr.sv

# Top: the chain wrapper
$CONVERTERS_ROOT/rtl/axi4_dwidth_to_axil4_wr_chain.sv
