# Filelist for stream_char_top — FPGA synthesis target for Nexys A7-100T.
# Wraps stream_char_harness with board I/O (clock, reset button, UART, LEDs).

# Pull in the full harness (which in turn pulls in STREAM top + UART bridge).
-f $STREAM_CHAR_ROOT/rtl/filelists/stream_char_harness.f

# CDC-isolated LED driver and the 2-phase handshake it uses.
$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv
$STREAM_CHAR_ROOT/rtl/led_status_driver.sv

# Board-level top (pins + harness instantiation only).
$STREAM_CHAR_ROOT/rtl/stream_char_top.sv
