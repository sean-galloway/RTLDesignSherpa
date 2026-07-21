# Filelist for rapids_char_top — FPGA synthesis / lint target for Nexys A7-100T.
# Location: projects/NexysA7/rapids_characterization/flows-rapids-beats/flists/rapids_char_top.f
#
# Wraps rapids_char_harness with board I/O (clock, reset button, UART, LEDs,
# 7-seg) plus the host front-end (UART->AXIL bridge, AXIL slave decode/router,
# apb_master for the DUT-register path). Sources shared with the harness or the
# converter filelists resolve to the same absolute path and are de-duplicated.

# ---- The characterization harness (+ DUT + pattern/mem blocks + incdirs) ----
-f $REPO_ROOT/projects/NexysA7/rapids_characterization/flows-rapids-beats/flists/rapids_char_harness.f

# ---- Host front-end: UART <-> AXIL master (uart_rx/tx, axil4_master_wr/rd,
#      gaxi_skid_buffer) ----
-f $REPO_ROOT/projects/components/converters/rtl/filelists/uart_axil_bridge.f

# ---- AXIL-slave cmd/rsp -> APB (reuses gaxi_skid_buffer from the bridge f) ----
-f $REPO_ROOT/rtl/amba/filelists/apb_master.f

# ---- Board status helpers: LED bank + 7-seg (+ their deps) ----
-f $REPO_ROOT/rtl/amba/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/led_status_driver.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/seven_seg_4digit.sv

# ---- Verilator-only Xilinx primitive stub (BUFG); guarded by `ifdef VERILATOR
#      so Vivado ignores it and uses the real unisim BUFG at synthesis ----
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/verilator_xilinx_stubs.sv

# ---- Board-level top (pins + host front-end + harness instantiation) ----
$REPO_ROOT/projects/NexysA7/rapids_characterization/flows-rapids-beats/rtl/rapids_char_top.sv
