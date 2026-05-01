# Filelist for stream_char_top — FPGA synthesis target for Nexys A7-100T.
# Wraps stream_char_harness with board I/O (clock, reset button, UART, LEDs).

# Pull in the full harness — which itself pulls the framework's
# instrumentation library (including the LED driver and 7-seg display
# modules used by this top).
-f $STREAM_CHAR_ROOT/rtl/filelists/stream_char_harness.f

# Per-build configuration package (side-Q depths, delay queue capacities).
# Swap this line to a variant package file (same package name, different
# parameter values) to rebuild a different config without touching RTL.
$STREAM_CHAR_ROOT/rtl/stream_char_cfg_pkg.sv

# Board-level top (pins + harness instantiation only).
$STREAM_CHAR_ROOT/rtl/stream_char_top.sv
