# Filelist for axi_read_engine module (Beats-specific)
# Location: projects/components/rapids/rtl/filelists/fub_beats/axi_read_engine_beats.f
# Purpose: Multi-channel AXI4 read engine with space-aware arbitration (STREAM-based, beats mode)

# Include directories
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files (MUST be first, in dependency order)
# Monitor packages - common first, then protocol-specific, then unified
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv

# Dependencies - Arbiter
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv

# AXI read engine module
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/axi_read_engine_beats.sv
