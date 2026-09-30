# LiteDRAM apples-to-apples characterization harness -- the LINT closure.
# Everything except litedram_core (Xilinx primitives; Vivado only) and the
# pin-level top that instantiates it, so `make lint` elaborates
# char_engine_harness with verilator. The board build reads
# litedram_char_board.f, which layers the core + top on this list.
#
# Deliberately the SAME collateral build-perf's ddr2_char_harness.f pulls,
# minus the DFI shims: the two flows must measure through identical RTL.
# Root path token is $REPO_ROOT.

+incdir+$REPO_ROOT/rtl/amba/includes

# UART -> AXIL host bridge
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/uart_axil_bridge.f

# Generated 1 -> 6 AXIL bridge (same address map as build-perf)
-f $REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/rtl/bridges/filelists/bridge_ddr2_char_axil.f

# The DUT-agnostic engine, from the shared framework.
#
# This used to pull ddr2_char_macro.f -- the PUMICE macro's filelist -- purely
# to reach char_engine_block, and its own comment conceded the consequence:
# "pumice itself rides along parsed-but-unreferenced". The whole DDR2
# controller was compiled into the build that exists to be pumice's yardstick.
# char_engine_block.f carries the engine and nothing else, so the comparison
# build no longer contains the thing it is comparing against.
-f $REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/filelists/char_engine_block.f

# AXIL SRAM slave for the debug_sram / dfi_mon_ram slots
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axil_axil.f

# Verilator-only Xilinx primitive stubs (BUFG in led_status_driver). Wrapped
# in `ifdef VERILATOR so Vivado never sees them.
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f

# 7-segment glyph decoder + framework blocks
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f
# The framework's OWN package. It must precede harness_csr, which takes
# mem_variant_e from it. It used to take memtype_e from pumice_pkg -- see
# mem_char_pkg.sv for why that was wrong in both directions.
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/mem_char_pkg.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/harness_csr.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/led_status_driver.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/rtl/seven_seg_4digit.sv

# DUT-agnostic engine harness (build-perf's ddr2_char_harness without pumice)
$REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/rtl/char_engine_harness.sv
