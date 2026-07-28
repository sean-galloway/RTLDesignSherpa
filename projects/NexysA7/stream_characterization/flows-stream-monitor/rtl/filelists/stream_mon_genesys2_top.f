# Filelist for stream_mon_genesys2_top -- Genesys 2 (Kintex-7 XC7K325T-2)
# monitor COVERAGE build (8 channels, USE_AXI_MONITORS=1, profile tally on).
# Location: projects/NexysA7/stream_characterization/flows-stream-monitor/rtl/filelists/stream_mon_genesys2_top.f
#
# Vivado-only target (IBUFDS / MMCME2_BASE / BUFG are Xilinx unisim primitives
# supplied by Vivado). Mirrors the flows-stream-bridge genesys2 filelist.

# The full monitor harness (STREAM top + in-core monitors, dma_slave_monitors,
# the two profile tallies + their cfg AXIL slaves, the bridge, UART). Also pulls
# stream_mon_cfg_pkg.sv, which defines package stream_char_cfg_pkg (the config
# variant the top references).
-f $STREAM_CHAR_ROOT/rtl/filelists/stream_mon_harness.f

# Genesys 2 board wrapper (MMCM clocking + pin-level I/O).
$STREAM_CHAR_ROOT/rtl/stream_mon_genesys2_top.sv
