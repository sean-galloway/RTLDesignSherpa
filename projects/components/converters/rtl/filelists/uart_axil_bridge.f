# Filelist for uart_axil_bridge module
# Location: projects/components/converters/rtl/filelists/uart_axil_bridge.f
# Purpose: UART to AXI4-Lite master bridge with timing isolation

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies - UART modules
$CONVERTERS_ROOT/rtl/uart_to_axil4/uart_rx.sv
$CONVERTERS_ROOT/rtl/uart_to_axil4/uart_tx.sv

# Dependencies - AXI4-Lite timing isolation
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_rd.sv

# Main module
$CONVERTERS_ROOT/rtl/uart_to_axil4/uart_axil_bridge.sv
