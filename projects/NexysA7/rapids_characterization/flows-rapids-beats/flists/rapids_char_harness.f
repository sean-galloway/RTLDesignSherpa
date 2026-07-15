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
+incdir+$REPO_ROOT/rtl/common/includes
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/projects/components/stream/rtl/includes

# ---- DUT: split RAPIDS beats top (+ all its deps) ----
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/top_beats/rapids_beats_top.f

# ---- CRC + LFSR leaves (not pulled by the DUT filelist) ----
$REPO_ROOT/rtl/common/dataint_crc_xor_shift.sv
$REPO_ROOT/rtl/common/dataint_crc_xor_shift_cascade.sv
$REPO_ROOT/rtl/common/dataint_crc.sv
$REPO_ROOT/rtl/common/shifter_lfsr_fibonacci.sv

# ---- AXI4 skid leaves + SDPRAM/addr-gen core (deps of the memory/pattern blocks) ----
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv
$REPO_ROOT/rtl/amba/shared/sdpram_core.sv

# ---- On-chip pattern generators / checkers + memories ----
$REPO_ROOT/rtl/amba/shared/axi4_slave_rd_pattern_gen.sv
$REPO_ROOT/rtl/amba/shared/axi4_slave_wr_crc_check.sv
$REPO_ROOT/rtl/amba/shared/axi_bus_meter.sv
$REPO_ROOT/rtl/amba/shared/axis_bus_meter.sv
$REPO_ROOT/rtl/amba/shared/axis4_master_pattern_gen.sv
$REPO_ROOT/rtl/amba/shared/axis4_slave_pattern_check.sv
$REPO_ROOT/rtl/amba/shared/sdpram_slave_axi4_axi4.sv

# ---- Harness top ----
$REPO_ROOT/projects/NexysA7/rapids_characterization/flows-rapids-beats/rtl/rapids_char_harness.sv
