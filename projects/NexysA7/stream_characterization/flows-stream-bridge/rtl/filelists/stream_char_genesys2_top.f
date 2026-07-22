# Filelist for stream_char_genesys2_top — Genesys 2 (Kintex-7 XC7K325T-2)
# monitor board-validation build (4 channels, USE_AXI_MONITORS=1).
# Location: projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/filelists/stream_char_genesys2_top.f
#
# Same harness + config package as the Nexys A7 top; only the board wrapper
# differs (IBUFDS / MMCME2_BASE / BUFG are Xilinx unisim primitives supplied
# by Vivado — this is a Vivado-only target, mirroring the rapids_char
# genesys2 filelist pattern).

# Pull in the full harness (STREAM top, UART/AXIL bridge, instrumentation
# library including the LED status driver used by this top).
-f $STREAM_CHAR_ROOT/rtl/filelists/stream_char_harness.f

# Per-build configuration package (side-Q depths, delay queue capacities).
$STREAM_CHAR_ROOT/rtl/stream_char_cfg_pkg.sv

# Genesys 2 board wrapper (MMCM clocking + pin-level I/O).
$STREAM_CHAR_ROOT/rtl/stream_char_genesys2_top.sv
