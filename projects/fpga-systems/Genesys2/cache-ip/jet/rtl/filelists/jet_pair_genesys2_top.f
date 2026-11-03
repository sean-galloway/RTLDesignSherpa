#==============================================================================
# jet_pair_genesys2_top.f
#==============================================================================
# Compile closure for the jet pair-rig Genesys2 board top.
#==============================================================================

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/cache-ip/common-ip/rtl/includes

# Reset macro header
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared cache package and core closure
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# jet package
-f $JET_ROOT/rtl/filelists/jet_pkg.f

# jet_top + its deps (monlite transports, ACE snoop slave, sdpram, monbus arbiter)
-f $JET_ROOT/rtl/filelists/jet_top.f

# Pair fabric
-f $JET_ROOT/rtl/filelists/jet_pair_fabric.f

# UART -> AXIL bridge
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f

# Generated 1x6 bridge for this harness
-f $JET_FRAMEWORK_ROOT/rtl/bridges/filelists/bridge_jet_axil.f

# MonBus group + tally
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_group_1wr.f
-f $MISC_ROOT/rtl/filelists/monbus_tally_axil.f

# Verilator-only Xilinx primitive stubs for lint.
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f

# House modules used by amber_cycle_injector (family-alignment)
-f $MISC_ROOT/rtl/filelists/dma_address_gen.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f

# Shared harness collateral: amber_cycle_injector is area-agnostic
$AMBER_FRAMEWORK_ROOT/rtl/amber_cycle_injector.sv

# New area RTL
$JET_FRAMEWORK_ROOT/rtl/jet_pair_harness.sv
$JET_FRAMEWORK_ROOT/rtl/jet_pair_genesys2_top.sv
