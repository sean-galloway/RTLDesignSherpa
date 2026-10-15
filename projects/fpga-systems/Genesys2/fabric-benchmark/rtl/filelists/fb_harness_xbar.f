# fb_harness, leg xbar (sim): the common harness plus the AXI Crossbar with the
# Verilator primitive models; the Vivado flow uses fb_data_fabric_xbar.f instead.
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_harness_common.f
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_data_fabric_xbar_sim.f
