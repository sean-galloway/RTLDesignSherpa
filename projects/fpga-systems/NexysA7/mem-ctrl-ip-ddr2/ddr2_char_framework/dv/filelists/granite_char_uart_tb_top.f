# Filelist for granite_char_uart_tb_top — cocotb TB around the FULL granite_char_harness
# (real UART bridge + harness_csr + 1->N AXIL bridge + engines + the storage-less
# granite controller), with the DFI wired to internal phy_dfi_* nets for the
# DFISlavePHY BFM.
#
# Mirrors dv/filelists/ddr2_char_uart_tb_top.f with the harness swapped to the
# granite target: granite_char_macro.f (engines + granite_top_geared) replaces
# ddr2_char_macro.f, and the granite harness source replaces ddr2_char_harness.sv.
# Omits the FPGA pin top and the a7ddrphy stub/adapter (not simulatable).

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/uart_axil_bridge.f
-f $REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/rtl/bridges/filelists/bridge_ddr2_char_axil.f
-f $REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite/rtl/filelists/granite_char_macro.f

-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axil_axil.f
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/dfi_cmd_delay.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/dfi_rddata_delay.sv
# The framework's OWN package. It must precede harness_csr, which takes
# mem_variant_e from it.
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/mem_char_pkg.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/harness_csr.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/led_status_driver.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/rtl/seven_seg_4digit.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite/rtl/granite_char_harness.sv

$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tb/granite_char_uart_tb_top.sv
