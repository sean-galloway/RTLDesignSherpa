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
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f

# Misc test infrastructure (pattern gen + CRC check)
# dataint_crc depends on dataint_crc_xor_shift_cascade and dataint_crc_xor_shift
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift_cascade.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_pattern_gen.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_crc_check.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_dma_slaves.f

# Shared instrumentation library (axi_response_delay, harness_csr, decoder,
# bridges, RAMs, board-level status drivers).
-f $STREAM_CHAR_FRAMEWORK_ROOT/rtl/filelists/instrumentation.f

# RFC Stage E: external DMA observer, instantiated inline (in parallel with the
# in-core monitors) for the observer-vs-in-core equivalence cosim. Its meter +
# latency-hist + mon-tap deps are already pulled via stream_top_ch8.f above;
# only the observer wrapper and its AXIL-read / AXI4-write monbus output stage
# are new here.
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axi4_group.f
# axi4_dma_observer RETIRED 2026-08-14 (superseded by projects/components/misc/rtl/axi4_intf_master_observer.sv).
# This tree is reference-only and no longer elaborates.

# Flow-specific top-level harness wrapper (instantiates STREAM + the
# instrumentation library above).
$STREAM_CHAR_ROOT/rtl/stream_char_harness.sv
