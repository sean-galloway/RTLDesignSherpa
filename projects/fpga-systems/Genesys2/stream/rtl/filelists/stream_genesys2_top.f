# Filelist for stream_genesys2_top -- Genesys 2 (Kintex-7 XC7K325T-2)
# monitor COVERAGE build (8 channels, USE_AXI_MONITORS=1, profile tally on).
# Location: projects/fpga-systems/Genesys2/stream/build-mon/rtl/filelists/stream_genesys2_top.f
#
# IBUFDS / MMCME2_BASE / BUFG are Xilinx unisim primitives supplied by Vivado at
# synthesis. The shared verilator-only stubs below let `make lint` elaborate
# this top without the vendor library (same mechanism pumice uses).

# The full monitor harness (STREAM top + in-core monitors, dma_slave_monitors,
# the two profile tallies + their cfg AXIL slaves, the bridge, UART). Also pulls
# stream_cfg_pkg.sv, which defines package stream_char_cfg_pkg (the config
# variant the top references).
-f $FRAMEWORK_ROOT/rtl/filelists/stream_harness.f

# Verilator-only Xilinx primitive stubs (BUFG / IBUFDS / MMCME2_BASE). Wrapped
# in `ifdef VERILATOR, so Vivado ignores the file and uses the real unisims.
# Shared by every board flow (misc/ owns the compile closure; -f include it
# rather than naming the .sv, so a consumer never hand-lists another area).
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f

# Genesys 2 board wrapper (MMCM clocking + pin-level I/O).
$FRAMEWORK_ROOT/rtl/stream_genesys2_top.sv
