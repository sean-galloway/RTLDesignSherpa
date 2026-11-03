#==============================================================================
# jet_pair_harness_host_tb.f
#==============================================================================
# Compile closure for the direct-host AXIL testbench wrapper.
# Reuses the board top filelist (the board top itself is compiled but unused;
# the wrapper instantiates jet_pair_harness directly with USE_DIRECT_HOST=1).
#==============================================================================

-f $JET_FRAMEWORK_ROOT/rtl/filelists/jet_pair_genesys2_top.f

# Testbench wrapper
$JET_FRAMEWORK_ROOT/dv/jet_pair_harness_host_tb.sv
