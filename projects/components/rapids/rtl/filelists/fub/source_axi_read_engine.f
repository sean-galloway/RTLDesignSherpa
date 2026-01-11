# RAPIDS Source AXI Read Engine FUB File List (Chunk-based)
# Location: projects/components/rapids/rtl/filelists/fub/source_axi_read_engine.f
# Purpose: Source AXI read engine module (original RAPIDS, chunk mode)

# Include directories
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes

# Package files (MUST be first, in dependency order)
# Monitor packages - common first, then protocol-specific, then unified
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/fub/source_axi_read_engine.sv
