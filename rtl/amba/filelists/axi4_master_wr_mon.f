# Filelist for axi4_master_wr_mon module
# Location: rtl/amba/filelists/axi4_master_wr_mon.f
#
# Purpose: AXI4 Master Write Ocelus with integrated filtering
#
# Architecture: Combines axi4_master_wr with axi_monitor_filtered for
# transaction monitoring with configurable packet filtering

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files (MUST be compiled before modules that import them)
$REPO_ROOT/rtl/amba/includes/ocelus_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_pkg.sv

# Dependencies - Common utilities (used by ocelus infrastructure)
-f $REPO_ROOT/rtl/common/filelists/arbiter_priority_encoder.f
-f $REPO_ROOT/rtl/common/filelists/counter_load_clear.f
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f

# Dependencies - Ocelus Infrastructure (order matters - base modules first)
$REPO_ROOT/rtl/amba/ocelus/monitor_trans_cam.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_trans_mgr.sv
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_timer.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_timeout.sv
# Reporter sub-blocks (must precede the reporter top wrapper)
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_error.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_timeout.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_compl.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_threshold.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_perf.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter_debug.sv
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_reporter.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_addr_check.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_base.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_filtered.sv

# Dependencies - GAXI Skid Buffers (used by axi4_master_wr)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Dependencies - AXI4 Master Write (core functionality)
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv

# This module - AXI4 Master Write Ocelus
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon.sv
