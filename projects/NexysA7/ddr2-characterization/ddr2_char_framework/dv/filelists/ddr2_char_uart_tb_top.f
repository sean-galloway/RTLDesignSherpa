# Filelist for ddr2_char_uart_tb_top — cocotb TB around the FULL ddr2_char_harness
# (real UART bridge + harness_csr + 1->N AXIL bridge + engines + pumice controller),
# with the DFI wired to internal phy_dfi_* nets for the DFISlavePHY BFM.
#
# Mirrors flows-ours-uart/rtl/filelists/ddr2_char_harness.f but OMITS the FPGA
# synthesis top (ddr2_char_top.sv) and the a7ddrphy stub / DFI->PHY adapter
# (not simulatable in verilator), and adds this TB top.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/converters/rtl/filelists/uart_axil_bridge.f
-f $REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/filelists/bridge_ddr2_char_axil.f
-f $REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/ddr2_char_macro.f

-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axil_axil.f
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/verilator_xilinx_stubs.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/dfi_cmd_delay.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/dfi_rddata_delay.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/harness_csr.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/led_status_driver.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/seven_seg_4digit.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/flows-ours-uart/rtl/ddr2_char_harness.sv

$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/dv/tb/ddr2_char_uart_tb_top.sv
