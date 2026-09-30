# Filelist for rapids_top (RAPIDS beats DMA top-level, SPLIT core)
# Location: projects/components/dma-ip/rapids/rtl/filelists/top/rapids_top.f
#
# Builds the split RAPIDS beats top:
#   - rapids_core (thin wrapper over rapids_src + rapids_snk,
#     with the shared scheduler array included ONCE) via rapids_core.f
#   - MonBus AXI-Lite group (single merged egress)
#   - APB -> reg chain: apb4_slave, peakrdl_to_cmdrsp (the kick windows are
#     ordinary registers now, so no separate kick block is built)
#   - rapids_regs (PeakRDL, split SRC/SNK) + rapids_config_block (x2) + top
#
# The data-engine portion is modeled on rapids_core.f, which is already
# deduplicated (both half filelists pull the scheduler array, so it is included
# once). Sources referenced by more than one filelist resolve to the same
# absolute path and are de-duplicated by the loader.

# Include directories
# reset_defs.svh -- this module uses `ALWAYS_FF_RST, so its macro header
# must be on the include path and compiled before it.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/projects/components/dma-ip/stream/rtl/includes

# ---- RAPIDS beats core (two independent halves + wrapper) ----
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/rapids_core.f

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
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axil4_group.f

-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f

# ---- Always-on data-path bus meters ----
# rapids_top instantiates axi_bus_meter twice (read + write) to give the
# RDMON_/WRMON_PERF_* CSRs a source. Pulled in by its own sub-block filelist,
# per the closure rule stated above.
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f

# ---- APB -> register chain ----
-f $REPO_ROOT/projects/components/dma-ip/stream/rtl/filelists/stream_pkg.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# ---- PeakRDL register file (split SRC/SNK) ----
$REPO_ROOT/projects/components/dma-ip/rapids/regs/generated/rtl/rapids_regs_pkg.sv
$REPO_ROOT/projects/components/dma-ip/rapids/regs/generated/rtl/rapids_regs.sv

# ---- Config mapping + top ----
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro_beats/rapids_config_block.sv
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/top/rapids_top.sv
