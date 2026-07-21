# RAPIDS MonBus AXI-Lite Group Macro File List
# Description: Aggregates monitor bus streams with filtering and AXI-Lite interfaces

# Include directories
+incdir+$REPO_ROOT/projects/components/dmas/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes

# Package files (MUST be first, in dependency order)
# Monitor packages - common first, then protocol-specific, then unified
# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil_axil_group.f
-f $REPO_ROOT/rtl/common/filelists/fifo_sync.f

$REPO_ROOT/projects/components/dmas/rapids/rtl/includes/rapids_pkg.sv

# Monbus group core family (cam/compressor/core + div-by-3 helper) -- shared
# canonical list so a new core dependency is added in ONE place.
-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f

# RAPIDS 2-input wrapper: monbus_arbiter(2) + the shared AXIL/AXIL group
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro/monbus_axil_group_2in.sv
