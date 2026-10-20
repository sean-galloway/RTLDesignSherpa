# Bridge stress model -- Genesys 2 board top, third-party IP build (bridge_bs_xil).
# The AMD/Xilinx IP (bs_atg, bs_cdma, bs_bram_ctrl, bs_bram, bs_pc_*) is created
# in the Vivado project by fpga/tcl/bs_xil_ip.tcl, and the LiteDRAM core
# (bs_litedram, generated toolchain output) is added there too: not listed here.
-f $REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/generated/filelists/bs_harness_bridge_bs_xil.f
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bs_genesys2_xil_top.sv
