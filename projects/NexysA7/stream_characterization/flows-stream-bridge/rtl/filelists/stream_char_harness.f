# Filelist for stream_char_harness (full characterization integration)
# Location: projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/filelists/stream_char_harness.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$STREAM_ROOT/regs/generated/rtl

# Pull in the complete STREAM top (all deps, packages, monitors)
-f $STREAM_ROOT/rtl/filelists/top/stream_top_ch8.f

# UART to AXIL bridge
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f

# AXIL slave modules (needed by monbus_axil_group inside stream_top_ch8)
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_wr.sv

# Misc test infrastructure (pattern gen + CRC check)
# dataint_crc depends on dataint_crc_xor_shift_cascade and dataint_crc_xor_shift
$REPO_ROOT/rtl/common/dataint_crc_xor_shift.sv
$REPO_ROOT/rtl/common/dataint_crc_xor_shift_cascade.sv
$REPO_ROOT/rtl/common/dataint_crc.sv
$REPO_ROOT/rtl/common/shifter_lfsr_fibonacci.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/shared/axi4_slave_rd_pattern_gen.sv
$REPO_ROOT/rtl/amba/shared/axi4_slave_wr_crc_check.sv
$REPO_ROOT/rtl/amba/shared/axi4_dma_slaves.sv

# Shared instrumentation library (axi_response_delay, harness_csr, decoder,
# bridges, RAMs, board-level status drivers).
-f $FRAMEWORK_ROOT/rtl/filelists/instrumentation.f

# RFC Stage E: external DMA observer, instantiated inline (in parallel with the
# in-core monitors) for the observer-vs-in-core equivalence cosim. Its meter +
# latency-hist + mon-tap deps are already pulled via stream_top_ch8.f above;
# only the observer wrapper and its AXIL-read / AXI4-write monbus output stage
# are new here.
$REPO_ROOT/rtl/amba/shared/monbus_axil_axi4_group.sv
$REPO_ROOT/rtl/amba/shared/axi4_dma_observer.sv

# Flow-specific top-level harness wrapper (instantiates STREAM + the
# instrumentation library above).
$STREAM_CHAR_ROOT/rtl/stream_char_harness.sv
