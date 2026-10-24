# Filelist for rapids_byte_harness (RAPIDS beats characterization harness)
# Location: projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/filelists/rapids_byte_harness.f
#
# Builds the synthesizable characterization harness that wraps the split
# rapids_beats_top DUT with on-chip pattern generators/checkers + memories:
#   - rapids_beats_top          (DUT, via its own filelist below)
#   - axis4_master_injector  / axis4_slave_pattern_check  (AXIS stimulus/check)
#   - axi4_slave_rd_injector / axi4_slave_wr_crc_check     (512b data src/sink)
#   - sdpram_slave_axi4_axi4 x4 (descriptor RAM x2 + control semaphore RAM x2)
#
# The DUT filelist below already provides the AMBA package set, gaxi leaves,
# monbus infra, etc. Sources referenced by more than one filelist resolve to
# the same absolute path and are de-duplicated by the loader.

# ---- Include directories ----
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/projects/components/dma-ip/stream/rtl/includes

# ---- DUT: split RAPIDS beats top (+ all its deps) ----
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/top_beats/rapids_beats_top.f
# byte-granular RAPIDS (rapids TASK-019); selected by BYTE_DUT=1
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/top/rapids_top.f
# rapids-g (rapids TASK-034): the same top with firmware schedulers; selected by
# the RAPIDS_G define (make RAPIDS_G=1). Only the selected top is elaborated.
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/top_g/rapids_g_top.f

-f $REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/filelists/rapids_byte_harness_common.f
