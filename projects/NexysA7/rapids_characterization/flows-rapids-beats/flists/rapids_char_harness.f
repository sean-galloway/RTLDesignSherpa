# Filelist for rapids_char_harness (RAPIDS beats characterization harness)
# Location: projects/NexysA7/rapids_characterization/flows-rapids-beats/flists/rapids_char_harness.f
#
# Builds the synthesizable characterization harness that wraps the split
# rapids_beats_top DUT with on-chip pattern generators/checkers + memories:
#   - rapids_beats_top          (DUT, via its own filelist below)
#   - axis4_master_pattern_gen  / axis4_slave_pattern_check  (AXIS stimulus/check)
#   - axi4_slave_rd_pattern_gen / axi4_slave_wr_crc_check     (512b data src/sink)
#   - sdpram_slave_axi4_axi4 x4 (descriptor RAM x2 + control semaphore RAM x2)
#
# The DUT filelist below already provides the AMBA package set, gaxi leaves,
# monbus infra, etc. Sources referenced by more than one filelist resolve to
# the same absolute path and are de-duplicated by the loader.

# ---- Include directories ----
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/dmas/rapids/rtl/includes
+incdir+$REPO_ROOT/projects/components/dmas/stream/rtl/includes

# ---- DUT: split RAPIDS beats top (+ all its deps) ----
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/top_beats/rapids_beats_top.f

# ---- CRC + LFSR leaves (not pulled by the DUT filelist) ----
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift_cascade.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f

# ---- AXI4 skid leaves + SDPRAM/addr-gen core (deps of the memory/pattern blocks) ----
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi_gen_addr.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f

# ---- On-chip pattern generators / checkers + memories ----
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_pattern_gen.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_crc_check.f
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/axis_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_master_pattern_gen.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_slave_pattern_check.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f

# ---- Harness top ----
$REPO_ROOT/projects/NexysA7/rapids_characterization/flows-rapids-beats/rtl/rapids_char_harness.sv
