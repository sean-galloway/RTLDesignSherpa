# Filelist for rapids_beats_top (RAPIDS beats DMA top-level, SPLIT core)
# Location: projects/components/dmas/rapids/rtl/filelists/top_beats/rapids_beats_top.f
#
# Builds the split RAPIDS beats top:
#   - rapids_core_beats (thin wrapper over rapids_src_beats + rapids_snk_beats,
#     with the shared scheduler array included ONCE) via rapids_core_beats.f
#   - MonBus AXI-Lite group (single merged egress)
#   - APB -> reg chain: apb4_slave, apbtodescr (x2), peakrdl_to_cmdrsp
#   - rapids_regs (PeakRDL, split SRC/SNK) + rapids_config_block (x2) + top
#
# The data-engine portion is modeled on rapids_core_beats.f, which is already
# deduplicated (both half filelists pull the scheduler array, so it is included
# once). Sources referenced by more than one filelist resolve to the same
# absolute path and are de-duplicated by the loader.

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes
+incdir+$REPO_ROOT/projects/components/dmas/rapids/rtl/includes
+incdir+$REPO_ROOT/projects/components/dmas/stream/rtl/includes

# ---- RAPIDS beats core (two independent halves + wrapper) ----
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/rapids_core_beats.f

# ---- MonBus AXI-Lite group (single merged egress) ----
# AXIL leaves + shared group core (monbus_group.f). The monitor_*_pkg packages,
# gaxi_skid_buffer / gaxi_fifo_sync / fifo_control / counter_bin leaves and the
# monbus_arbiter are already pulled in by the core filelist above.
# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil_axil_group.f

-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f

# ---- APB -> register chain ----
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/stream_pkg.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/fub/apbtodescr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# ---- PeakRDL register file (split SRC/SNK) ----
$REPO_ROOT/projects/components/dmas/rapids/regs/generated/rtl/rapids_regs_pkg.sv
$REPO_ROOT/projects/components/dmas/rapids/regs/generated/rtl/rapids_regs.sv

# ---- Config mapping + top ----
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/rapids_config_block.sv
$REPO_ROOT/projects/components/dmas/rapids/rtl/top_beats/rapids_beats_top.sv
