# Pin-level top for the Genesys 2 LiteDRAM DDR3 board proof.
#
# litedram_genesys2_ddr3.v is GENERATED and gitignored -- run ./regen.sh first.
# It is Xilinx-primitive soup that only Vivado reads in full; the `lint` target
# in the Makefile therefore elaborates this top with the Verilator stubs and
# lets Vivado be the authority on the core itself.
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f
# The CPU. litedram_gen does NOT emit this -- regen.sh copies it out of
# pythondata-cpu-vexriscv, because LiteX only does so during the gateware
# compile we skip. Without it synthesis dies 90 seconds in with
# "module 'VexRiscv' not found".
$REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/build-litedram/gen/gateware/VexRiscv.v
$REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/build-litedram/gen/gateware/litedram_genesys2_ddr3.v
$REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/build-litedram/rtl/litedram_ddr3_board_top.sv
