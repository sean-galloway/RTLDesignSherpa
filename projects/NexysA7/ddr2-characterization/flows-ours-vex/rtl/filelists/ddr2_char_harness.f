# Filelist for ddr2_char_harness (full DDR2 characterization integration)
# Location: projects/NexysA7/ddr2-characterization/flows-ours-vex/rtl/filelists/ddr2_char_harness.f
#
# Pulls in every dep the harness needs and lands the flow's harness +
# top on top. Root path token is $REPO_ROOT (points at RTLDesignSherpa).

+incdir+$REPO_ROOT/rtl/amba/includes

# UART -> AXIL host bridge
-f $REPO_ROOT/projects/components/converters/rtl/filelists/uart_axil_bridge.f

# Generated 1 -> 5 AXIL bridge for the DDR2 harness
-f $REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/filelists/bridge_ddr2_char_axil.f

# ddr2_char_macro (WR pattern-gen + RD CRC-check + ddr2-lpddr2 controller top)
-f $REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/ddr2_char_macro.f

# AXIL SRAM slave used for desc_ram / debug_sram / dfi_mon_ram
$REPO_ROOT/rtl/amba/axil4/axil4_slave_wr.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/shared/sdpram_core.sv
$REPO_ROOT/rtl/amba/shared/sdpram_slave_axil_axil.sv

# 7-segment glyph decoder used by seven_seg_4digit
$REPO_ROOT/rtl/common/hex_to_7seg.sv

# Verilator-only Xilinx primitive stubs (BUFG). Wrapped in `ifdef VERILATOR
# so Vivado doesn't see them.
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/verilator_xilinx_stubs.sv

# Flat DFI -> per-phase adapter + a7ddrphy black-box stub. Vivado excludes
# a7ddrphy_stub.sv and substitutes the LiteDRAM-generated a7ddrphy.v at
# build time; the stub is here so verilator / cocotb can lint the top.
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/dfi_v21_flat_to_a7ddrphy.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/a7ddrphy_stub.sv

# Framework blocks: harness_csr + board displays. axi_response_delay is
# committed under ddr2_char_framework/rtl/ but not yet instantiated in
# the harness — kept here so future response-delay wiring is a one-line
# swap-in.
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/harness_csr.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/led_status_driver.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/seven_seg_4digit.sv

# Flow-specific harness + FPGA pin-level top
$REPO_ROOT/projects/NexysA7/ddr2-characterization/flows-ours-vex/rtl/ddr2_char_harness.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/flows-ours-vex/rtl/ddr2_char_top.sv
