# Filelist for stream_char_top -- Nexys A7-100T (Artix-7 XC7A100T-1)
# characterization build (4 channels default, USE_AXI_MONITORS per build).
# Location: projects/fpga-systems/Genesys2/dma-ip/stream/rtl/filelists/stream_char_top.f
#
# The Nexys top is pins + reset sync + LED/7-seg only (no IBUFDS/MMCM), so the
# verilator_xilinx_stubs include is unnecessary but kept: it is ifdef VERILATOR
# and shared by every board flow, so a consumer never hand-lists another area.

# The full monitor harness (STREAM top + in-core monitors, the two profile
# tallies + their cfg AXIL slaves, the bridge, UART). Also pulls
# stream_cfg_pkg.sv, which defines package stream_char_cfg_pkg (the config
# variant the top references).
-f $FRAMEWORK_ROOT/rtl/filelists/stream_harness.f

# Verilator-only Xilinx primitive stubs (BUFG / IBUFDS / MMCME2_BASE). Wrapped
# in `ifdef VERILATOR, so Vivado ignores the file and uses the real unisims.
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f

# Nexys A7 board wrapper (100 MHz direct clocking + pin-level I/O).
$FRAMEWORK_ROOT/rtl/stream_char_top.sv
