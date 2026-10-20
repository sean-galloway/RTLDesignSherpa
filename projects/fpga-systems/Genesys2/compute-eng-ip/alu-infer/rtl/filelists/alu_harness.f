# Filelist for alu_harness -- the board harness for a valid/ready ALU.
# Location: projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/rtl/filelists/alu_harness.f
#
# The harness WITHOUT its device under test: a build supplies `alu_slot` and
# the ALU's own filelist (see build-*/rtl/filelists/).
# Roots: $REPO_ROOT, $CONVERTERS_ROOT.

+incdir+$REPO_ROOT/rtl/amba/includes

# AXI4-Lite -> APB4 -> PeakRDL cpuif
-f $CONVERTERS_ROOT/rtl/filelists/axi4_to_apb4_shim.f
-f $CONVERTERS_ROOT/rtl/filelists/apb4_to_peakrdl.f

# Generated CSRs (Rule 0.1: generated in their own dir) and the harness
$REPO_ROOT/projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/rtl/generated/alu_harness_regs/rtl/alu_harness_regs_pkg.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/rtl/generated/alu_harness_regs/rtl/alu_harness_regs.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/rtl/alu_harness.sv
