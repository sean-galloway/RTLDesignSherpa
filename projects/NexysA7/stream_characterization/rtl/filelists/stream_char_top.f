# Filelist for stream_char_top — FPGA synthesis target for Nexys A7-100T.
# Wraps stream_char_harness with board I/O (clock, reset button, UART, LEDs).

# Pull in the full harness (which in turn pulls in STREAM top + UART bridge).
-f $STREAM_CHAR_ROOT/rtl/filelists/stream_char_harness.f

# Board-level top (pins + harness instantiation only).
$STREAM_CHAR_ROOT/rtl/stream_char_top.sv
