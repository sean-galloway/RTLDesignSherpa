# RAPIDS Sink SRAM Controller Macro File List
# Location: projects/components/dmas/rapids/rtl/filelists/macro_beats/snk_sram_controller_beats.f
# Purpose: Multi-channel Sink SRAM Controller (Network Slave -> SRAM -> AXI Write Engine)
#
# The SRAM itself is STREAM's sram_controller; RAPIDS supplies only a naming
# wrapper (snk_sram_controller_beats.sv). RAPIDS previously carried its own
# copy of the macro and the per-channel unit, which drifted from STREAM and
# missed STREAM's bridge_occupancy double-count fix and its FIFO_BRAM setting.
# One implementation, two naming wrappers -- see the wrapper header.
#
# RAPIDS' own alloc_ctrl_beats / drain_ctrl_beats / latency_bridge_beats are NO
# LONGER pulled in here: this path uses STREAM's stream_alloc_ctrl /
# stream_drain_ctrl / stream_latency_bridge instead. Those RAPIDS FUBs keep
# their own tests and filelists and are still built by rapids_all.f.

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change.
#
# gaxi_fifo_sync.f already brings counter_bin.f and fifo_control.f, which are
# what stream_alloc_ctrl / stream_drain_ctrl need.

# Includes -- fifo_defs.svh and reset_defs.svh both live in rtl/amba/includes,
# so no STREAM include directory is required. None of STREAM's five SRAM files
# references stream_pkg (measured: 0 refs), so stream_pkg is NOT pulled in.
+incdir+$REPO_ROOT/rtl/amba/includes

# STREAM SRAM implementation: -f the OWNING area's filelist, never hand-list its
# sources. Hand-listing another area's files means tracking that area's internal
# dependencies by hand, and it silently rots when they change; the filelist
# contract check (bin/filelist_registry.py --audit) enforces this.
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/fub/sram_controller.f

# RAPIDS naming wrapper (must be last - instantiates sram_controller)
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/snk_sram_controller_beats.sv
