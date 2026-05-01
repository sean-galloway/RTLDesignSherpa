# Filelist: stream_char_framework/rtl/filelists/instrumentation.f
#
# Shared instrumentation library for stream characterization flows. Any
# fpga-flow that wraps a DMA on the Nexys A7 board pulls these in.
#
# Required env vars (Makefile sets them):
#   FRAMEWORK_ROOT - this framework's root (projects/NexysA7/stream_char_framework)

# Pipelined memory-controller delay queue (timestamp FIFO).
$FRAMEWORK_ROOT/rtl/axi_response_delay.sv

# AXIL fabric: 5-slave decoder + AXIL-to-APB bridge for the harness CSRs.
$FRAMEWORK_ROOT/rtl/axil_decode_5s.sv
$FRAMEWORK_ROOT/rtl/axil2apb.sv

# Harness CSRs (kick-burst, response-delay programming, cycle timer, status).
$FRAMEWORK_ROOT/rtl/harness_csr.sv

# Generic memory blocks (descriptor RAM and monitor trace SRAM).
$FRAMEWORK_ROOT/rtl/desc_ram.sv
$FRAMEWORK_ROOT/rtl/debug_sram.sv

# Board-level status outputs (LED bank + 7-segment display) and their
# upstream dependencies in the shared rtl/ tree.
$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv
$REPO_ROOT/rtl/common/hex_to_7seg.sv
$FRAMEWORK_ROOT/rtl/led_status_driver.sv
$FRAMEWORK_ROOT/rtl/seven_seg_4digit.sv
