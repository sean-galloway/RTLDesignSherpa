# Filelist for cdc_demo_uart_tb_top — cocotb TB around the FULL cdc_demo harness
# (real uart_axil_bridge + cdc_demo_harness + 4x cdc_counter_domain), with the
# per-counter ctr_clk driven as inputs from the cocotb test (behavioral async
# clocks in place of the unsimulatable MMCM/BUFGMUX tree in cdc_demo_top).

+incdir+$REPO_ROOT/rtl/amba/includes

# Real UART -> AXI4-Lite bridge (the equivalence boundary)
-f $REPO_ROOT/projects/components/converters/rtl/filelists/uart_axil_bridge.f

# common building blocks used by cdc_counter_domain (and its subdeps)
$REPO_ROOT/rtl/common/bin2gray.sv
$REPO_ROOT/rtl/common/gray2bin.sv
$REPO_ROOT/rtl/common/sync_pulse.sv
$REPO_ROOT/rtl/common/glitch_free_n_dff_arn.sv
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/counter_bingray.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/fifo_async.sv

# amba/shared CDC primitives (value-out path modes 1/3/4)
$REPO_ROOT/rtl/amba/shared/cdc_synchronizer.sv
$REPO_ROOT/rtl/amba/shared/cdc_open_loop.sv
$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv
$REPO_ROOT/rtl/amba/shared/cdc_4_phase_handshake.sv

# DUT: harness + counter domain + TB top
$REPO_ROOT/projects/NexysA7/cdc_counter_display/rtl/cdc_demo_harness.sv
$REPO_ROOT/projects/NexysA7/cdc_counter_display/rtl/cdc_counter_domain.sv
$REPO_ROOT/projects/NexysA7/cdc_counter_display/dv/tb/cdc_demo_uart_tb_top.sv
