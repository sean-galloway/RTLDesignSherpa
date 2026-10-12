#==============================================================================
# amber_pair_harness_host_tb.f
#==============================================================================
# Compile closure for the direct-host AXIL testbench wrapper.
# Reuses the board top filelist (the board top itself is compiled but unused;
# the wrapper instantiates amber_pair_harness directly with USE_DIRECT_HOST=1).
#==============================================================================

# Framework root for the amber Genesys2 area.
+incdir+$AMBER_FRAMEWORK_ROOT/rtl/includes

-f $AMBER_FRAMEWORK_ROOT/rtl/filelists/amber_pair_genesys2_top.f

# Testbench wrapper
$AMBER_FRAMEWORK_ROOT/dv/amber_pair_harness_host_tb.sv
