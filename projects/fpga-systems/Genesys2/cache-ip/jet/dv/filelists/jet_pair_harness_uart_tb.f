#==============================================================================
# jet_pair_harness_uart_tb.f
#==============================================================================
# Compile closure for the UART-bridge testbench wrapper.
# Reuses the board top filelist; the wrapper instantiates jet_pair_harness
# with USE_DIRECT_HOST=0 and exposes the UART rx/tx pins.
#==============================================================================

-f $JET_FRAMEWORK_ROOT/rtl/filelists/jet_pair_genesys2_top.f

# Testbench wrapper
$JET_FRAMEWORK_ROOT/dv/jet_pair_harness_uart_tb.sv
