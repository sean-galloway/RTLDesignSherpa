#==============================================================================
# amber_pair_genesys2_top.f
#==============================================================================
# Compile closure for the amber pair-rig Genesys2 board top.
#==============================================================================

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/cache-ip/common-ip/rtl/includes

# Reset macro header
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# amber package and core closure
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# amber_top + its deps (monlite transports, ACE snoop slave, sdpram, monbus arbiter)
-f $AMBER_ROOT/rtl/filelists/amber_top.f

# Pair fabric
-f $AMBER_ROOT/rtl/filelists/amber_pair_fabric.f

# UART -> AXIL bridge
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f

# Generated 1x6 bridge for this harness
-f $AMBER_FRAMEWORK_ROOT/rtl/bridges/filelists/bridge_amber_axil.f

# MonBus group + tally
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axil4_group.f
-f $MISC_ROOT/rtl/filelists/monbus_tally_axil.f

# Verilator-only Xilinx primitive stubs for lint.
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f

# House modules used by amber_cycle_injector (family-alignment)
-f $MISC_ROOT/rtl/filelists/dma_address_gen.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f

# New area RTL
$AMBER_FRAMEWORK_ROOT/rtl/amber_cycle_injector.sv
$AMBER_FRAMEWORK_ROOT/rtl/amber_pair_harness.sv
$AMBER_FRAMEWORK_ROOT/rtl/amber_pair_genesys2_top.sv
