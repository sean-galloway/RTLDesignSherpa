# Bridge stress model -- Genesys 2 board top, mixed AXI3 / AXI4 / AXI5 build
# with third-party IP (bridge_bs_xmix). The board top is build-xil's,
# with BS_XMIX: the xmix harness and its AXI3 bram port through bs_axi3_conv.
# The AMD/Xilinx IP (bs_xil_ip.tcl with BS_XMIX=1) and the LiteDRAM core are
# added in the Vivado project: not listed here.
+define+BS_XMIX
-f $REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/generated/filelists/bs_harness_bridge_bs_xmix.f
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bs_genesys2_xil_top.sv
