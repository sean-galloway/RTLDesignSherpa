# Filelist for kestrel_genesys2_top -- build-bram: kestrel behind kestrel_mem_bram.
# Location: projects/fpga-systems/Genesys2/riscv-ip/kestrel/build-bram/rtl/filelists/kestrel_genesys2_top.f
#
# The ONE compile closure for this build: `make lint` flattens it, the Vivado
# create_project.tcl expands it (dropping the verilator-only stubs).
# Roots: $REPO_ROOT, $CONVERTERS_ROOT, $KESTREL_ROOT.

+incdir+$REPO_ROOT/rtl/amba/includes

# The core and its registered-read memory system
-f $KESTREL_ROOT/rtl/filelists/top/kestrel_core.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_mem_bram.f

# Host UART front end
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f

# Lint/sim-only Xilinx primitive stubs (IBUFDS/MMCME2_BASE/BUFG); Vivado drops the file
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f

# Board top
$REPO_ROOT/projects/fpga-systems/Genesys2/riscv-ip/kestrel/rtl/kestrel_genesys2_top.sv
