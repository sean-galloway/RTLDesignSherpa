# Filelist for granite_char_harness (Granite DDR2/LPDDR2 characterization integration)
# Location: projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite/rtl/filelists/granite_char_harness.f
#
# Pulls in every dep the harness needs and lands the Granite harness + pin-level
# top on top. Root path token is $REPO_ROOT (points at RTLDesignSherpa).

+incdir+$REPO_ROOT/rtl/amba/includes

# UART -> AXIL host bridge
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/uart_axil_bridge.f

# Generated 1 -> 5 AXIL bridge for the DDR2 harness
-f $REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/rtl/bridges/filelists/bridge_ddr2_char_axil.f

# granite_char_macro (WR pattern-gen + RD CRC-check + Granite controller top)
-f $REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite/rtl/filelists/granite_char_macro.f

# AXIL SRAM slave used for debug_sram + dfi_mon_ram
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axil_axil.f

# 7-segment glyph decoder used by seven_seg_4digit
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f

# Verilator-only Xilinx primitive stubs (BUFG). Wrapped in `ifdef VERILATOR
# so Vivado doesn't see them.
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f

# Flat DFI -> per-phase adapter + a7ddrphy black-box stub. Vivado excludes
# a7ddrphy_stub.sv and substitutes the LiteDRAM-generated a7ddrphy.v at
# build time; the stub is here so verilator / cocotb can lint the top.
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/dfi_cmd_delay.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/dfi_rddata_delay.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/rtl/dfi_v21_flat_to_a7ddrphy.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/rtl/a7ddrphy_stub.sv

# Framework blocks: harness_csr + board displays.
# The framework's OWN package. It must precede harness_csr, which takes
# mem_variant_e from it.
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/mem_char_pkg.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/harness_csr.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/led_status_driver.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/rtl/seven_seg_4digit.sv

# Flow-specific harness + FPGA pin-level top
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite/rtl/granite_char_harness.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite/rtl/granite_char_top.sv
