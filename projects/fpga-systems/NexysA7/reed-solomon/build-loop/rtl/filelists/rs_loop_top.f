# Filelist for rs_loop_top -- the Reed-Solomon loop harness on the Nexys A7.
# Location: projects/fpga-systems/NexysA7/reed-solomon/build-loop/rtl/filelists/rs_loop_top.f
#
# The ONE compile closure for this build: `make lint` flattens it, the Vivado
# create_project.tcl expands it (dropping the verilator-only stubs), and the
# dv/ equivalence-sim filelist -f includes it.
#
# Roots: $REPO_ROOT, $CONVERTERS_ROOT (UART bridge + AXIL-to-cpuif adapter).

+incdir+$REPO_ROOT/rtl/amba/includes

# UART -> AXI4-Lite bridge and the AXI-Lite -> PeakRDL cpuif adapter
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f
-f $CONVERTERS_ROOT/rtl/filelists/axil4_to_peakrdl.f

# the codec under test, the injector, and the shared stream generator/checker
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_encoder_core.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_decoder_core.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_error_injector.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_master_pattern_gen.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_slave_pattern_check.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr.f

# Lint/sim-only Xilinx primitive stubs (IBUF/BUFG); Vivado drops the file
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f

# This build: geometry package, generated CSRs (Rule 0.1: generated in their own dir), harness, top
$REPO_ROOT/projects/fpga-systems/NexysA7/reed-solomon/build-loop/rtl/rs_loop_cfg_pkg.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/reed-solomon/build-loop/rtl/generated/rs_loop_regs/rtl/rs_loop_regs_pkg.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/reed-solomon/build-loop/rtl/generated/rs_loop_regs/rtl/rs_loop_regs.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/reed-solomon/build-loop/rtl/rs_loop_harness.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/reed-solomon/build-loop/rtl/rs_loop_top.sv
