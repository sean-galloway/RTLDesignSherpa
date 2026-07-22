# Filelist for stream_top_ch8 module (complete STREAM top-level with APB)
# Location: projects/components/dmas/stream/rtl/filelists/top/stream_top_ch8.f
#
# Architecture: Complete STREAM DMA with APB configuration interface
# - APB4 configuration interface (peakrdl_to_cmdrsp converter)
# - apbtodescr (channel kick-off router)
# - stream_config_block (register mapping)
# - stream_core (USE_AXI_MONITORS=0, monitors disabled)

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/apb_slave_cdc.f
-f $REPO_ROOT/rtl/amba/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/amba/filelists/cdc_4_phase_handshake.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil_axil_group.f

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# PeakRDL generated register package and module
# Verilator waiver: suppress MULTIDRIVEN on generated per-field always_comb blocks
$STREAM_ROOT/regs/stream_regs.vlt
$STREAM_ROOT/regs/generated/rtl/stream_regs_pkg.sv
$STREAM_ROOT/regs/generated/rtl/stream_regs.sv

# APB to CMD/RSP converter (used by stream_top for APB interface)
# Note: peakrdl_to_cmdrsp is a common utility block (should be in rtl/amba or rtl/common)
# For now, assuming it's in stream/rtl/fub (may need to relocate)
# TODO: Move peakrdl_to_cmdrsp to rtl/amba/apb/ if it's truly generic
# $STREAM_ROOT/rtl/fub/peakrdl_to_cmdrsp.sv

# APB kick-off router
-f $STREAM_ROOT/rtl/filelists/fub/apbtodescr.f

# CMD/RSP router (routes CMD/RSP from apb_slave_cdc to apbtodescr or peakrdl_to_cmdrsp)
# Address map: 0x000-0x03F → apbtodescr, 0x100-0x3FF → peakrdl_to_cmdrsp
$STREAM_ROOT/rtl/top/cmdrsp_router.sv

# PeakRDL adapter (from converters component)
-f $REPO_ROOT/projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# Configuration mapping block
# $STREAM_ROOT/rtl/top/stream_config_block.sv

# Include stream_core via its filelist
# Note: stream_top_ch8 instantiates stream_core with USE_AXI_MONITORS=0
-f $STREAM_ROOT/rtl/filelists/macro/stream_core.f
# Monbus group core family (cam/compressor/core + div-by-3 helper) -- shared.
-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f

# Top-level wrapper files (unique to this filelist)
$STREAM_ROOT/rtl/top/stream_config_block.sv
$STREAM_ROOT/rtl/top/stream_top_ch8.sv
