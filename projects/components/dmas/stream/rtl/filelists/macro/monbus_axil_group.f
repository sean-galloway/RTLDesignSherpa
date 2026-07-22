# Filelist for monbus_axil_group module
# Location: projects/components/dmas/stream/rtl/filelists/macro/monbus_axil_group.f
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

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil_axil_group.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Monbus group core family (cam + compressor + core + div-by-3 helper).
# Shared canonical list so a new core dependency is added in ONE place.
-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f
