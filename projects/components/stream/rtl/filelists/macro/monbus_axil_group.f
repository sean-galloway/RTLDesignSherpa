# Filelist for monbus_axil_group module
# Location: projects/components/stream/rtl/filelists/macro/monbus_axil_group.f
#
# Purpose: Monitor Bus AXI-Lite Group - Packet filtering and routing
#
# Architecture:
# - Single monitor bus input (STREAM is memory-to-memory only)
# - Per-protocol configurable packet filtering (drop, error/interrupt, master write)
# - Separate FIFOs for error/interrupt vs master write paths
# - AXI-Lite slave for error/interrupt read
# - AXI-Lite master for monitor bus packet writes
# - Protocol support: AXI, AXIS, CORE (3 protocols)

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

# Dependencies - Common utilities
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# Dependencies - GAXI FIFO (for error/interrupt and master write FIFOs)
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Dependencies - GAXI FIFO (for error/interrupt and master write FIFOs)
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr.sv

# Monbus group core family (cam + compressor + core + div-by-3 helper).
# Shared canonical list so a new core dependency is added in ONE place.
-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f

# AXIL/AXIL wrapper for this consumer (other family variants:
# monbus_axil_axi4_group.sv, monbus_axi4_axil_group.sv, monbus_axi4_axi4_group.sv).
$REPO_ROOT/rtl/amba/shared/monbus_axil_axil_group.sv
