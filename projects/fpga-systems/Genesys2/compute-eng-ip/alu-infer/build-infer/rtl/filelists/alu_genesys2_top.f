# Filelist for alu_genesys2_top -- build-infer: alu_infer_top in the ALU slot.
# Location: projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/build-infer/rtl/filelists/alu_genesys2_top.f
#
# The ONE compile closure for this build: `make lint` flattens it, the Vivado
# create_project.tcl expands it (dropping the verilator-only stubs), and the
# dv/ equivalence-sim filelist -f includes the slot + harness part of it.
# Roots: $REPO_ROOT, $CONVERTERS_ROOT.

+incdir+$REPO_ROOT/rtl/amba/includes

# The device under test and this build's slot wrapper
-f $REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/filelists/alu_infer_top.f
$REPO_ROOT/projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/build-infer/rtl/alu_slot.sv

# The harness and the host UART front end
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f
-f $REPO_ROOT/projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/rtl/filelists/alu_harness.f

# Lint/sim-only Xilinx primitive stubs (IBUFDS/MMCME2_BASE/BUFG); Vivado drops the file
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f

# Board top
$REPO_ROOT/projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/rtl/alu_genesys2_top.sv
