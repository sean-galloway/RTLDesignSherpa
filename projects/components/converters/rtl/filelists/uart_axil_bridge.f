# Filelist for uart_axil_bridge module
# Location: projects/components/converters/rtl/filelists/uart_axil_bridge.f
# Purpose: UART to AXI4-Lite master bridge with timing isolation

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Dependencies - UART modules
$CONVERTERS_ROOT/rtl/uart_to_axil4/uart_rx.sv
$CONVERTERS_ROOT/rtl/uart_to_axil4/uart_tx.sv

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/axil4_master_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_master_wr.f

# Main module
$CONVERTERS_ROOT/rtl/uart_to_axil4/uart_axil_bridge.sv
