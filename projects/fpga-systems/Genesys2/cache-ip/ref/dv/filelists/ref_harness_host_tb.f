#==============================================================================
# ref_harness_host_tb.f
#==============================================================================
# Compile closure for the direct-host AXIL testbench wrapper of the
# reference-cache rig. Reuses the board top filelist (the board top itself is
# compiled but unused; the wrapper instantiates ref_harness directly with
# USE_DIRECT_HOST=1).
#==============================================================================

-f $REF_FRAMEWORK_ROOT/rtl/filelists/ref_genesys2_top.f

# Testbench wrapper
$REF_FRAMEWORK_ROOT/dv/ref_harness_host_tb.sv
