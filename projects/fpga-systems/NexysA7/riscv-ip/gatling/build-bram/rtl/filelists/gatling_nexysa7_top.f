# Filelist for gatling_nexysa7_top -- build-bram: gatling behind gatling_mem_bram.
# Location: projects/fpga-systems/NexysA7/riscv-ip/gatling/build-bram/rtl/filelists/gatling_nexysa7_top.f
#
# The ONE compile closure for this build: `make lint` flattens it, the Vivado
# create_project.tcl expands it (dropping the verilator-only stubs).
# Roots: $REPO_ROOT, $CONVERTERS_ROOT, $GATLING_ROOT (and $KESTREL_ROOT, which
# gatling's core filelist uses for the fubs it shares with kestrel).

+incdir+$REPO_ROOT/rtl/amba/includes

# The barrel core and its block-RAM memory system
-f $GATLING_ROOT/rtl/filelists/top/gatling_core.f
-f $GATLING_ROOT/rtl/filelists/fub/gatling_mem_bram.f

# Host UART front end
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f

# Lint/sim-only Xilinx primitive stubs (MMCME2_BASE/BUFG); Vivado drops the file
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f

# Board top
$REPO_ROOT/projects/fpga-systems/NexysA7/riscv-ip/gatling/rtl/gatling_nexysa7_top.sv
