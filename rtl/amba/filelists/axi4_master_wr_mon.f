# Filelist for axi4_master_wr_mon module
# Location: rtl/amba/filelists/axi4_master_wr_mon.f
#
# Purpose: AXI4 Master Write Monitor with integrated filtering
#
# Architecture: Combines axi4_master_wr with axi_monitor_filtered for
# transaction monitoring with configurable packet filtering

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files (MUST be compiled before modules that import them)
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv

# Dependencies - Common utilities (used by monitor infrastructure)
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv

# Dependencies - Monitor Infrastructure (order matters - base modules first)
$REPO_ROOT/rtl/amba/shared/axi_monitor_trans_mgr.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timer.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timeout.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_base.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_filtered.sv

# Dependencies - GAXI Skid Buffers (used by axi4_master_wr)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Dependencies - AXI4 Master Write (core functionality)
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv

# This module - AXI4 Master Write Monitor
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon.sv
