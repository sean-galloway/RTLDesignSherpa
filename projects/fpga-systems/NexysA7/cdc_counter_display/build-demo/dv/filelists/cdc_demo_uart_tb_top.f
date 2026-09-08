# Filelist for cdc_demo_uart_tb_top -- cocotb TB around the FULL cdc_demo
# harness (real uart_axil_bridge + cdc_demo_harness + 4x cdc_counter_domain),
# with the per-counter ctr_clk driven as inputs from the cocotb test
# (behavioral async clocks in place of the unsimulatable MMCM/BUFGMUX tree in
# cdc_demo_top).
#
# The DUT closure is the BUILD's own filelist, so sim, lint and synthesis
# compile the same design; only the TB top is added here. (cdc_demo_top and
# the verilator stubs come along in the closure -- unused by this TB top, and
# discarded at elaboration.)

-f $REPO_ROOT/projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/rtl/filelists/cdc_demo_top.f

# TB top
$REPO_ROOT/projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/dv/tb/cdc_demo_uart_tb_top.sv
