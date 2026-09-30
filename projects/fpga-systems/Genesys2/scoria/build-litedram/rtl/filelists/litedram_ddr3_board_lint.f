# LINT-ONLY closure for the board top: the generated core replaced by its
# blackbox stub. The real core is Xilinx-primitive soup (OSERDESE2, ODELAYE2,
# IDELAYCTRL, OBUFDS) that Verilator cannot elaborate, so linting against it
# reports 50+ MODMISSING errors that say nothing about this design.
#
# The stub is GENERATED from the core by bin/gen_core_blackbox.py, so the
# interface checked here is the interface the core actually has. This catches a
# mis-wired port; Vivado remains the authority on the core itself, and
# litedram_ddr3_board.f is the list the BUILD uses.
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/verilator_xilinx_stubs.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/scoria/build-litedram/rtl/litedram_genesys2_ddr3_bb.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/scoria/build-litedram/rtl/litedram_ddr3_board_top.sv
