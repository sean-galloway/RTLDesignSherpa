#==============================================================================
# ref_genesys2_top.f -- reference-cache rig Genesys2 top (cache-ip common-ip TASK-003)
#==============================================================================
# The jet pair rig's board top and harness with the vendored OpenHW HPDcache
# in the cache slot (ref_hpdcache_top), ref_null_cache for the second
# injector and ref_axil_stub on the tally apertures. Same bridge, injector,
# memory, UART and clocking as the jet rig. Env: REPO_ROOT, REF_FRAMEWORK_ROOT,
# JET_FRAMEWORK_ROOT (the shared bridge), AMBER_FRAMEWORK_ROOT (the injector),
# CACHE_COMMON_ROOT, CONVERTERS_ROOT, MISC_ROOT (see build-bringup/Makefile).
#==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/cache-ip/common-ip/rtl/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# geometry package (AMBER_* parameters) only
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# the reference caches (vendor/cv-hpdcache and vendor/cva6-dcache + wrappers);
# REF_CACHE_SEL on the top picks one
-f $REF_FRAMEWORK_ROOT/rtl/filelists/ref_hpdcache_top.f
-f $REF_FRAMEWORK_ROOT/rtl/filelists/ref_cva6_dcache_top.f

# UART -> AXIL, the shared jet bridge, the house AXI4 block-RAM slave
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f
-f $JET_FRAMEWORK_ROOT/rtl/bridges/filelists/bridge_jet_axil.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f

# the cycle injector and what it instantiates
-f $MISC_ROOT/rtl/filelists/dma_address_gen.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f
$AMBER_FRAMEWORK_ROOT/rtl/amber_cycle_injector.sv

$REF_FRAMEWORK_ROOT/rtl/ref_null_cache.sv
$REF_FRAMEWORK_ROOT/rtl/ref_axil_stub.sv
$REF_FRAMEWORK_ROOT/rtl/ref_harness.sv
$REF_FRAMEWORK_ROOT/rtl/ref_genesys2_top.sv
