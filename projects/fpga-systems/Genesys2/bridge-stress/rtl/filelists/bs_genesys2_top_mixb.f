# Bridge stress model -- Genesys 2 board top, single-beat DUT build (bridge_bs_mixed_b).
-f $REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/generated/filelists/bs_harness_bridge_bs_mixed_b.f
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bs_genesys2_top.sv
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f
