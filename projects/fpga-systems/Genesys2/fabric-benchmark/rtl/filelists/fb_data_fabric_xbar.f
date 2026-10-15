# Leg B1 data fabric under test: Xilinx AXI Crossbar v2.1, from the Vivado
# install (unencrypted HDL; XILINX_VIVADO is set by Vivado's settings64.sh and
# by this area's Makefile). The same files serve Verilator and Vivado, so the
# sim runs the RTL the bitstream is built from.
+incdir+$XILINX_VIVADO/data/ip/xilinx/axi_infrastructure_v1_1/hdl
$XILINX_VIVADO/data/ip/xilinx/generic_baseblocks_v2_1/hdl/generic_baseblocks_v2_1_vl_rfs.v
$XILINX_VIVADO/data/ip/xilinx/axi_infrastructure_v1_1/hdl/axi_infrastructure_v1_1_vl_rfs.v
$XILINX_VIVADO/data/ip/xilinx/axi_register_slice_v2_1/hdl/axi_register_slice_v2_1_vl_rfs.v
$XILINX_VIVADO/data/ip/xilinx/axi_data_fifo_v2_1/hdl/axi_data_fifo_v2_1_vl_rfs.v
$XILINX_VIVADO/data/ip/xilinx/axi_crossbar_v2_1/hdl/axi_crossbar_v2_1_vl_rfs.v
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/generated/fb_data_fabric_xbar/fb_data_fabric.sv
