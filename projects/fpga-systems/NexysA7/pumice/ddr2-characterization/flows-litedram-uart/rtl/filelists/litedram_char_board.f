# LiteDRAM apples-to-apples characterization harness -- the BOARD build.
# The lint closure plus the pin-level top and the generated LiteDRAM core.
# Vivado only: litedram_core.v instantiates Xilinx primitives.

-f $REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/rtl/filelists/litedram_char_harness.f

# Pin-level top: litedram_core + char_engine_harness on user_clk
$REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/rtl/litedram_char_top.sv

# LiteDRAM generated core (real a7ddrphy). Regenerate WITH a functional BIOS
# first:  ./regen.sh --bios   (litedram_hp.yml: 75 MHz sys / 1:2 / DDR2-300)
$REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/build_board/gateware/litedram_core.v

# The core's BIOS CPU. litedram_gen emits litedram_core.tcl pointing at
# VexRiscv.v INSIDE the LiteX venv, an absolute path that dies with the venv,
# so regen.sh copies it next to the core and this list uses that copy.
$REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/build_board/gateware/VexRiscv.v
