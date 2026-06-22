# Filelist: stream_char_framework/rtl/filelists/instrumentation.f
#
# Shared instrumentation library for stream characterization flows. Any
# fpga-flow that wraps a DMA on the Nexys A7 board pulls these in.
#
# Required env vars (Makefile sets them):
#   FRAMEWORK_ROOT - this framework's root (projects/NexysA7/stream_characterization/stream_char_framework)

# Pipelined memory-controller delay queue (timestamp FIFO).
$FRAMEWORK_ROOT/rtl/axi_response_delay.sv

# AXIL fabric: generator-driven 1->6 AXIL bridge with APB auto-conversion
# on the STREAM config slot and an AXIL bridge port (S5 = dma_axil) for the
# Vivado MCDMA / future Vivado bridge flows.
-f $FRAMEWORK_ROOT/rtl/bridges/filelists/bridge_stream_char_axil.f

# Harness CSRs (kick-burst, response-delay programming, cycle timer, status).
$FRAMEWORK_ROOT/rtl/harness_csr.sv

# (axi_bus_meter.sv retired from the harness in RFC Stage E.4 -- the per-cycle
#  valid/ready bucket counters are now in-core in stream_core, pulled in via
#  stream_core.f. Listing it here too would just create a MODDUP.)

# Unified SDP-BRAM slave -- protocol-agnostic compute kernel + thin
# per-permutation wrappers (no string-switch generate plumbing).
#   sdpram_core            -- BRAM + axi_gen_addr + clear FSM + obs
#   sdpram_slave_axi4_axi4 -- desc_ram (256-bit AXI4 wr + AXI4 rd)
#   sdpram_slave_axil_axil -- debug_sram (64-bit AXIL wr + AXIL rd)
# Requires axi_gen_addr (combinational per-beat address generator) and
# the standard axi4_slave_rd/wr + axil4_slave_rd/wr protocol skids
# (already pulled in via the bridge filelist).
$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv
$REPO_ROOT/rtl/amba/shared/sdpram_core.sv
$REPO_ROOT/rtl/amba/shared/sdpram_slave_axi4_axi4.sv
$REPO_ROOT/rtl/amba/shared/sdpram_slave_axil_axil.sv

# Sim-only scoreboard bound into stream_core's u_sram_controller. Catches
# per-channel data swaps between the RD-engine deposit and WR-engine drain
# sides. Pure `ifndef SYNTHESIS so FPGA build sees a zero-port module.
$FRAMEWORK_ROOT/rtl/sram_chan_tracker.sv
$FRAMEWORK_ROOT/rtl/sram_chan_tracker_bind.sv

# Board-level status outputs (LED bank + 7-segment display) and their
# upstream dependencies in the shared rtl/ tree.
$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv
$REPO_ROOT/rtl/common/hex_to_7seg.sv
$FRAMEWORK_ROOT/rtl/led_status_driver.sv
$FRAMEWORK_ROOT/rtl/seven_seg_4digit.sv
