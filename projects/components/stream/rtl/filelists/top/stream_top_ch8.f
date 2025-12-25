# Filelist for stream_top_ch8 module (complete STREAM top-level with APB)
# Location: projects/components/stream/rtl/filelists/top/stream_top_ch8.f
#
# Architecture: Complete STREAM DMA with APB configuration interface
# - APB4 configuration interface (peakrdl_to_cmdrsp converter)
# - apbtodescr (channel kick-off router)
# - stream_config_block (register mapping)
# - stream_core (USE_AXI_MONITORS=0, monitors disabled)

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# PeakRDL generated register package and module
$STREAM_ROOT/regs/generated/rtl/stream_regs_pkg.sv
$STREAM_ROOT/regs/generated/rtl/stream_regs.sv

# APB to CMD/RSP converter (used by stream_top for APB interface)
# Note: peakrdl_to_cmdrsp is a common utility block (should be in rtl/amba or rtl/common)
# For now, assuming it's in stream/rtl/fub (may need to relocate)
# TODO: Move peakrdl_to_cmdrsp to rtl/amba/apb/ if it's truly generic
# $STREAM_ROOT/rtl/fub/peakrdl_to_cmdrsp.sv

# APB kick-off router
-f $STREAM_ROOT/rtl/filelists/fub/apbtodescr.f

# GAXI modules for CDC
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/shared/cdc_handshake.sv

# APB slave modules (conditional CDC based on CDC_ENABLE parameter)
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc.sv  # With CDC (pclk ≠ aclk)
$REPO_ROOT/rtl/amba/apb/apb_slave.sv      # Without CDC (pclk = aclk)

# CMD/RSP router (routes CMD/RSP from apb_slave_cdc to apbtodescr or peakrdl_to_cmdrsp)
# Address map: 0x000-0x03F → apbtodescr, 0x100-0x3FF → peakrdl_to_cmdrsp
$STREAM_ROOT/rtl/top/cmdrsp_router.sv

# PeakRDL adapter (from converters component)
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

# Configuration mapping block
# $STREAM_ROOT/rtl/top/stream_config_block.sv

# Include stream_core via its filelist
# Note: stream_top_ch8 instantiates stream_core with USE_AXI_MONITORS=0
-f $STREAM_ROOT/rtl/filelists/macro/stream_core.f

# MonBus to AXI-Lite converter (used when USE_AXI_MONITORS=1)
$STREAM_ROOT/rtl/macro/monbus_axil_group.sv

# Top-level wrapper files (unique to this filelist)
$STREAM_ROOT/rtl/top/stream_config_block.sv
$STREAM_ROOT/rtl/top/stream_top_ch8.sv
