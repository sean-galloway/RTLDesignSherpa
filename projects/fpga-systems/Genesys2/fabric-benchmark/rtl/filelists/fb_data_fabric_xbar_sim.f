# SIM ONLY: Leg B1 plus Verilator models of the Xilinx primitives its
# C_FAMILY="kintex7" configuration instantiates (SRLC32E, MUXF7). Vivado
# supplies the real primitives, so the bitstream reads fb_data_fabric_xbar.f;
# the cosim reads this one. The configuration is the board's -- no rtl-family
# substitute -- and the models are functional, exact to the unisims.
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_data_fabric_xbar.f
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f
