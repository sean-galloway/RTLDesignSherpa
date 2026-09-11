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
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes

# UART -> AXIL host bridge
-f $REPO_ROOT/projects/components/converters/rtl/filelists/uart_axil_bridge.f

# Generated 1 -> 6 AXIL bridge (same address map as build-perf)
-f $REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/rtl/bridges/filelists/bridge_ddr2_char_axil.f

# char_engine_block (chargen_regs + char_gen_unit generator array + perf) and
# its deps. ddr2_char_macro.f is the list that owns them; pumice itself rides
# along parsed-but-unreferenced (nothing under litedram_char_top reaches it).
-f $REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/rtl/ddr2_char_macro.f

# AXIL SRAM slave for the debug_sram / dfi_mon_ram slots
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axil_axil.f

# Verilator-only Xilinx primitive stubs (BUFG in led_status_driver). Wrapped
# in `ifdef VERILATOR so Vivado never sees them.
-f $REPO_ROOT/projects/components/misc/rtl/filelists/verilator_xilinx_stubs.f

# 7-segment glyph decoder + framework blocks
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f
$REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/rtl/harness_csr.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/rtl/led_status_driver.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/rtl/seven_seg_4digit.sv

# DUT-agnostic engine harness (build-perf's ddr2_char_harness without pumice)
$REPO_ROOT/projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/rtl/char_engine_harness.sv
