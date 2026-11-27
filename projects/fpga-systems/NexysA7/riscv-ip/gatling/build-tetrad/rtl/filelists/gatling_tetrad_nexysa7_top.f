# Filelist for gatling_tetrad_nexysa7_top -- build-tetrad: gatling_tetrad on the Nexys A7.
# Location: projects/fpga-systems/NexysA7/riscv-ip/gatling/build-tetrad/rtl/filelists/gatling_tetrad_nexysa7_top.f
#
# The ONE compile closure for this build: `make lint` flattens it, the Vivado
# create_project.tcl expands it (dropping the verilator-only stubs).

-f $REPO_ROOT/projects/fpga-systems/NexysA7/riscv-ip/gatling/build-tetrad/rtl/filelists/gatling_tetrad_rig.f

# Lint/sim-only Xilinx primitive stubs (MMCME2_BASE/BUFG); Vivado drops the file
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f

# Board top
$REPO_ROOT/projects/fpga-systems/NexysA7/riscv-ip/gatling/rtl/gatling_tetrad_nexysa7_top.sv
