# Filelist for cdc_demo_uart_tb_top — cocotb TB around the FULL cdc_demo harness
# (real uart_axil_bridge + cdc_demo_harness + 4x cdc_counter_domain), with the
# per-counter ctr_clk driven as inputs from the cocotb test (behavioral async
# clocks in place of the unsimulatable MMCM/BUFGMUX tree in cdc_demo_top).

+incdir+$REPO_ROOT/rtl/amba/includes

# Real UART -> AXI4-Lite bridge (the equivalence boundary)
-f $REPO_ROOT/projects/components/converters/rtl/filelists/uart_axil_bridge.f

# common building blocks used by cdc_counter_domain (and its subdeps)
-f $REPO_ROOT/rtl/cdc/filelists/bin2gray.f
-f $REPO_ROOT/rtl/cdc/filelists/gray2bin.f
-f $REPO_ROOT/rtl/common/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/common/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_bingray.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/cdc/filelists/fifo_async.f

# amba/shared CDC primitives (value-out path modes 1/3/4)
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_open_loop.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f

# DUT: harness + counter domain + TB top
$REPO_ROOT/projects/NexysA7/cdc_counter_display/rtl/cdc_demo_harness.sv
$REPO_ROOT/projects/NexysA7/cdc_counter_display/rtl/cdc_counter_domain.sv
$REPO_ROOT/projects/NexysA7/cdc_counter_display/dv/tb/cdc_demo_uart_tb_top.sv
