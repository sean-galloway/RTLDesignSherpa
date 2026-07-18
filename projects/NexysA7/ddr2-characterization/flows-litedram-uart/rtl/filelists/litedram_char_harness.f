# Filelist for the LiteDRAM apples-to-apples characterization harness.
# Reuses the SAME engines + perf + csr + uart collateral as the pumice flow
# (ddr2_char_macro.f pulls the engines/perf/pumice_pkg; pumice itself is parsed
# but not reachable from litedram_char_top, so it is not synthesized). Root path
# token is $REPO_ROOT.

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes

# UART -> AXIL host bridge
-f $REPO_ROOT/projects/components/converters/rtl/filelists/uart_axil_bridge.f

# Engines (WR pattern-gen + RD CRC-check) + axi_bus_meter + pumice_pkg + deps
-f $REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/ddr2_char_macro.f

# 7-segment glyph decoder + framework blocks
$REPO_ROOT/rtl/common/hex_to_7seg.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/harness_csr.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/led_status_driver.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/seven_seg_4digit.sv

# DUT-agnostic engine harness + LiteDRAM pin-level top
$REPO_ROOT/projects/NexysA7/ddr2-characterization/flows-litedram-uart/rtl/char_engine_harness.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/flows-litedram-uart/rtl/litedram_char_top.sv

# LiteDRAM generated core (Vivado build only — real a7ddrphy; not verilatable).
# Regenerate WITH a functional BIOS first:  ./regen.sh --bios
$REPO_ROOT/projects/NexysA7/ddr2-characterization/flows-litedram-uart/build_board/gateware/litedram_core.v
