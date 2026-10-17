#==============================================================================
# amber_pair_harness_uart_tb.f
#==============================================================================
# Compile closure for the UART-bridge testbench wrapper.
# Reuses the board top filelist; the wrapper instantiates amber_pair_harness
# with USE_DIRECT_HOST=0 and exposes the UART rx/tx pins.
#==============================================================================

-f $AMBER_FRAMEWORK_ROOT/rtl/filelists/amber_pair_genesys2_top.f

# Testbench wrapper
$AMBER_FRAMEWORK_ROOT/dv/amber_pair_harness_uart_tb.sv
