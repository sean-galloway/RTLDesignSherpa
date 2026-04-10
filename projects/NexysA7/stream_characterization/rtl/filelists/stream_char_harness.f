# Filelist for stream_char_harness (full characterization integration)
# Location: projects/NexysA7/stream_characterization/rtl/filelists/stream_char_harness.f

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
$MISC_ROOT/rtl/axi4_slave_rd_pattern_gen.sv
$MISC_ROOT/rtl/axi4_slave_wr_crc_check.sv

# Characterization harness modules
$STREAM_CHAR_ROOT/rtl/axil_decode_5s.sv
$STREAM_CHAR_ROOT/rtl/axil2apb.sv
$STREAM_CHAR_ROOT/rtl/harness_csr.sv
$STREAM_CHAR_ROOT/rtl/desc_ram.sv
$STREAM_CHAR_ROOT/rtl/debug_sram.sv
$STREAM_CHAR_ROOT/rtl/stream_char_harness.sv
