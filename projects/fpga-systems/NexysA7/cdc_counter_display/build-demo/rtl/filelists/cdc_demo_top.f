# Filelist for cdc_demo_top -- the phase-2 UART-harness CDC demo build.
# Location: projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/rtl/filelists/cdc_demo_top.f
#
# The ONE compile closure for this build: `make lint` flattens it, the Vivado
# create_project.tcl expands it (dropping the verilator-only stubs), and the
# dv/ equivalence-sim filelist -f includes it -- so lint, synthesis and sim
# cannot compile different designs.
#
# Roots: $REPO_ROOT (repo libraries), $CONVERTERS_ROOT (UART bridge component).

+incdir+$REPO_ROOT/rtl/amba/includes

# Real UART -> AXI4-Lite bridge (component-owned closure: uart_rx/tx,
# axil4 master halves, gaxi skid/fifo, reset_defs)
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f

# common/cdc building blocks used by cdc_counter_domain (and its subdeps)
-f $REPO_ROOT/rtl/cdc/filelists/bin2gray.f
-f $REPO_ROOT/rtl/cdc/filelists/gray2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/cdc/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_bingray.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/cdc/filelists/fifo_async.f

# shared CDC primitives (value-out path modes 1/3/4)
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_open_loop.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f

# clock generation used by the board top
-f $REPO_ROOT/rtl/common/filelists/clock_divider.f

# Lint/sim-only Xilinx primitive stubs (IBUF/BUFG/BUFGMUX_CTRL/MMCME2_BASE).
# `ifdef VERILATOR guarded; the Vivado tcl additionally drops the file so the
# real unisims are used at synthesis.
-f $REPO_ROOT/projects/components/misc/rtl/filelists/verilator_xilinx_stubs.f

# This build's RTL
$REPO_ROOT/projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/rtl/cdc_demo_harness.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/rtl/cdc_counter_domain.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/rtl/cdc_demo_top.sv
