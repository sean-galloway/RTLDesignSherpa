# Instrumentation for the monitor harness — identical to the shared
# instrumentation.f but pulls bridge_stream_mon_axil (2 tally SRAMs + 2 err
# ports) instead of the perf bridge. Do NOT pull both bridges (adapter module
# names collide).
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/axi_response_delay.sv
-f $STREAM_CHAR_FRAMEWORK_ROOT/rtl/bridges/filelists/bridge_stream_mon_axil.f
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/harness_csr.sv
-f $REPO_ROOT/rtl/amba/filelists/axi_gen_addr.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axil_axil.f
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/sram_chan_tracker.sv
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/sram_chan_tracker_bind.sv
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/led_status_driver.sv
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/seven_seg_4digit.sv
