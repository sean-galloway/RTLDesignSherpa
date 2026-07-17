# Filelist for rapids_beats_top (RAPIDS beats DMA top-level, SPLIT core)
# Location: projects/components/dmas/rapids/rtl/filelists/top_beats/rapids_beats_top.f
#
# Builds the split RAPIDS beats top:
#   - rapids_core_beats (thin wrapper over rapids_src_beats + rapids_snk_beats,
#     with the shared scheduler array included ONCE) via rapids_core_beats.f
#   - MonBus AXI-Lite group (single merged egress)
#   - APB -> reg chain: apb_slave, apbtodescr (x2), peakrdl_to_cmdrsp
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
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr.sv
-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f
$REPO_ROOT/rtl/amba/shared/monbus_axil_axil_group.sv

# ---- APB -> register chain ----
$REPO_ROOT/projects/components/dmas/stream/rtl/includes/stream_pkg.sv
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/projects/components/dmas/stream/rtl/fub/apbtodescr.sv
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

# ---- PeakRDL register file (split SRC/SNK) ----
$REPO_ROOT/projects/components/dmas/rapids/regs/generated/rtl/rapids_regs_pkg.sv
$REPO_ROOT/projects/components/dmas/rapids/regs/generated/rtl/rapids_regs.sv

# ---- Config mapping + top ----
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/rapids_config_block.sv
$REPO_ROOT/projects/components/dmas/rapids/rtl/top_beats/rapids_beats_top.sv
