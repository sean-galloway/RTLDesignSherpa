# Bridge stress model -- build-xmix, Verilator lint only: the board top with
# port stubs for the AMD/Xilinx IP (bin/gen_xil_lint_stubs.py --xmix) and the
# Xilinx primitive stubs. Vivado reads bs_genesys2_top_xmix.f instead.
-f $REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/filelists/bs_genesys2_top_xmix.f
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/lint/bs_xmix_ip_stubs.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/litedram/bb/bs_litedram_bb.sv
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f
