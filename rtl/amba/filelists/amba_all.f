# ==============================================================================
# RTL AMBA Protocol Infrastructure - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: Complete list of all AMBA modules for linting with proper dependencies
# Usage:   verilator --lint-only -f filelists/amba_all.f
#
# Notes:
#   - Package files MUST be listed first (monitor_pkg, axi_pkg, apb_pkg)
#   - Modules that import packages depend on packages being compiled first
#   - Files organized by protocol for maintainability
#   - Self-contained: the rtl/common, rtl/math and rtl/cdc blocks these modules
#     instantiate arrive by -f include at the bottom. This list used to rely on
#     the Makefile passing -I$REPO_ROOT/rtl/common as a module SEARCH path,
#     which silently stopped resolving when math_* and the CDC set split out.
#
# ==============================================================================

# =============================================================================
# PACKAGES (MUST BE FIRST - ORDER MATTERS FOR DEPENDENCIES)
# =============================================================================
# Monitor packages - must be in dependency order
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
# Protocol packages
$REPO_ROOT/rtl/amba/includes/axi_pkg.sv
$REPO_ROOT/rtl/amba/includes/apb_pkg.sv
$REPO_ROOT/rtl/amba/includes/apb5_pkg.sv

# =============================================================================
# SHARED INFRASTRUCTURE (Base modules used by multiple protocols)
$REPO_ROOT/rtl/amba/shared/axi4_dma_observer.sv
$REPO_ROOT/rtl/amba/shared/axi4_dma_slaves.sv
# Both shared modules below instantiate dma_address_gen, which lives in
# projects/components/misc. -f its list rather than naming the path.
-f $REPO_ROOT/projects/components/misc/rtl/filelists/dma_address_gen.f
$REPO_ROOT/rtl/amba/shared/axi4_master_rd_crc_check.sv
$REPO_ROOT/rtl/amba/shared/axi4_master_wr_pattern_gen.sv
$REPO_ROOT/rtl/amba/shared/axi4_slave_rd_pattern_gen.sv
$REPO_ROOT/rtl/amba/shared/axi4_slave_wr_crc_check.sv
$REPO_ROOT/rtl/amba/shared/axi_bus_meter.sv
$REPO_ROOT/rtl/amba/shared/axi_perf_latency_hist.sv
$REPO_ROOT/rtl/amba/shared/axis4_master_pattern_gen.sv
$REPO_ROOT/rtl/amba/shared/axis4_slave_pattern_check.sv
$REPO_ROOT/rtl/amba/shared/axis_bus_meter.sv
$REPO_ROOT/rtl/amba/shared/sdpram_core.sv
$REPO_ROOT/rtl/amba/shared/sdpram_slave_axi4_axi4.sv
$REPO_ROOT/rtl/amba/shared/sdpram_slave_axi4_axil.sv
$REPO_ROOT/rtl/amba/shared/sdpram_slave_axil_axi4.sv
$REPO_ROOT/rtl/amba/shared/sdpram_slave_axil_axil.sv

# =============================================================================
$REPO_ROOT/rtl/amba/shared/amba_clock_gate_ctrl.sv
$REPO_ROOT/rtl/amba/monitor/arbiter_monbus_common.sv
$REPO_ROOT/rtl/amba/monitor/arbiter_rr_pwm_monbus.sv
$REPO_ROOT/rtl/amba/monitor/arbiter_wrr_pwm_monbus.sv
$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv
$REPO_ROOT/rtl/amba/shared/axi_master_rd_splitter.sv
$REPO_ROOT/rtl/amba/shared/axi_master_wr_splitter.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_base.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_filtered.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_compl.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_debug.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_error.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_perf.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_threshold.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_timeout.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_timeout.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_timer.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_trans_mgr.sv
$REPO_ROOT/rtl/amba/shared/axi_split_combi.sv
$REPO_ROOT/rtl/amba/monitor/monbus_arbiter.sv

# =============================================================================
# GAXI - Generic AXI Utilities (FIFOs, Skid Buffers)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer_dbldrn.sv

# =============================================================================
$REPO_ROOT/rtl/amba/gaxi/gaxi_drop_fifo_sync.sv
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_regslice.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_skid_buffer_async.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer_struct.sv

# =============================================================================
# APB - Advanced Peripheral Bus
# =============================================================================
$REPO_ROOT/rtl/amba/apb/apb_master.sv
$REPO_ROOT/rtl/amba/apb/apb_master_cg.sv
$REPO_ROOT/rtl/amba/apb/apb_master_stub.sv
$REPO_ROOT/rtl/amba/apb/apb_monitor.sv
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc_cg.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cg.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_stub.sv

# =============================================================================
# AXI4 - Advanced eXtensible Interface (Full)
# =============================================================================
# AXI4 Master Read
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_cg.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon_cg.sv

# AXI4 Master Write
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_cg.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon_cg.sv

# AXI4 Slave Read
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd_cg.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd_mon_cg.sv

# AXI4 Slave Write
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr_cg.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr_mon_cg.sv

# AXI4 Stubs (Test support)
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_master_rd_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_master_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_master_wr_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_rd_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_wr_stub.sv

# =============================================================================
# AXI4-Lite - AXI4 Subset (Single beat transactions only)
# =============================================================================
# AXIL4 Master Read
$REPO_ROOT/rtl/amba/axil4/axil4_master_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_rd_cg.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_rd_mon.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_rd_mon_cg.sv

# AXIL4 Master Write
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr_cg.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr_mon.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr_mon_cg.sv

# AXIL4 Slave Read
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd_cg.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd_mon.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd_mon_cg.sv

# AXIL4 Slave Write
$REPO_ROOT/rtl/amba/axil4/axil4_slave_wr.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_wr_cg.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_wr_mon.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_wr_mon_cg.sv

# =============================================================================
# AXIS - AXI Stream
# =============================================================================
$REPO_ROOT/rtl/amba/axis4/axis_master.sv
$REPO_ROOT/rtl/amba/axis4/axis_master_cg.sv
$REPO_ROOT/rtl/amba/axis4/axis_slave.sv
$REPO_ROOT/rtl/amba/axis4/axis_slave_cg.sv

# ==============================================================================
# =============================================================================
# APB5 - Advanced Peripheral Bus v5
# =============================================================================
$REPO_ROOT/rtl/amba/apb5/apb5_master.sv
$REPO_ROOT/rtl/amba/apb5/apb5_master_cg.sv
$REPO_ROOT/rtl/amba/apb5/apb5_master_stub.sv
$REPO_ROOT/rtl/amba/apb5/apb5_slave.sv
$REPO_ROOT/rtl/amba/apb5/apb5_slave_cdc.sv
$REPO_ROOT/rtl/amba/apb5/apb5_slave_cdc_cg.sv
$REPO_ROOT/rtl/amba/apb5/apb5_slave_cg.sv
$REPO_ROOT/rtl/amba/apb5/apb5_slave_stub.sv

# =============================================================================
# AXI5 - Advanced eXtensible Interface v5
# =============================================================================
$REPO_ROOT/rtl/amba/axi5/axi5_master_rd.sv
$REPO_ROOT/rtl/amba/axi5/axi5_master_rd_cg.sv
$REPO_ROOT/rtl/amba/axi5/axi5_master_wr.sv
$REPO_ROOT/rtl/amba/axi5/axi5_master_wr_cg.sv
$REPO_ROOT/rtl/amba/axi5/axi5_slave_rd.sv
$REPO_ROOT/rtl/amba/axi5/axi5_slave_rd_cg.sv
$REPO_ROOT/rtl/amba/axi5/axi5_slave_wr.sv
$REPO_ROOT/rtl/amba/axi5/axi5_slave_wr_cg.sv
$REPO_ROOT/rtl/amba/axi5/stubs/axi5_master_rd_stub.sv
$REPO_ROOT/rtl/amba/axi5/stubs/axi5_master_stub.sv
$REPO_ROOT/rtl/amba/axi5/stubs/axi5_master_wr_stub.sv
$REPO_ROOT/rtl/amba/axi5/stubs/axi5_slave_rd_stub.sv
$REPO_ROOT/rtl/amba/axi5/stubs/axi5_slave_stub.sv
$REPO_ROOT/rtl/amba/axi5/stubs/axi5_slave_wr_stub.sv

# =============================================================================
# AXIS5 - AXI Stream v5
# =============================================================================
$REPO_ROOT/rtl/amba/axis5/axis5_master.sv
$REPO_ROOT/rtl/amba/axis5/axis5_master_cg.sv
$REPO_ROOT/rtl/amba/axis5/axis5_slave.sv
$REPO_ROOT/rtl/amba/axis5/axis5_slave_cg.sv

# =============================================================================
# CDC - Clock Domain Crossing primitives
# =============================================================================
# The CDC area owns these now (AMBA-CDC-REORG). amba modules that DEPEND on one
# -f include it; the standalone crossings (2/4-phase handshake, open_loop) are
# linted by rtl/cdc/filelists/cdc_all.f, not from here.
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f

# =============================================================================
# MONITOR SUBSYSTEM (protocol monitors, monbus, CAM)
# =============================================================================
$REPO_ROOT/rtl/amba/apb5/apb5_monitor.sv
$REPO_ROOT/rtl/amba/monitor/apb_monitor_addr_check.sv
$REPO_ROOT/rtl/amba/axi5/axi5_master_rd_mon.sv
$REPO_ROOT/rtl/amba/axi5/axi5_master_rd_mon_cg.sv
$REPO_ROOT/rtl/amba/axi5/axi5_master_wr_mon.sv
$REPO_ROOT/rtl/amba/axi5/axi5_master_wr_mon_cg.sv
$REPO_ROOT/rtl/amba/axi5/axi5_slave_rd_mon.sv
$REPO_ROOT/rtl/amba/axi5/axi5_slave_rd_mon_cg.sv
$REPO_ROOT/rtl/amba/axi5/axi5_slave_wr_mon.sv
$REPO_ROOT/rtl/amba/axi5/axi5_slave_wr_mon_cg.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_addr_check.sv
$REPO_ROOT/rtl/amba/monitor/monbus_axi4_axi4_group.sv
$REPO_ROOT/rtl/amba/monitor/monbus_axi4_axil_group.sv
$REPO_ROOT/rtl/amba/monitor/monbus_axil_axi4_group.sv
$REPO_ROOT/rtl/amba/monitor/monbus_axil_axil_group.sv
$REPO_ROOT/rtl/amba/monitor/monbus_cam.sv
$REPO_ROOT/rtl/amba/monitor/monbus_cam_pipe.sv
$REPO_ROOT/rtl/amba/monitor/monbus_compressor.sv
$REPO_ROOT/rtl/amba/monitor/monbus_group_core.sv
$REPO_ROOT/rtl/amba/monitor/monbus_halfbeat_packer.sv
$REPO_ROOT/rtl/amba/monitor/monitor_trans_cam.sv

# End of filelist
# ==============================================================================

# =============================================================================
# CROSS-AREA DEPENDENCIES (-f, never hand-listed -- see [[filelists]])
# =============================================================================
# common_all.f carries math_all.f itself, so this reaches rtl/math too.
-f $REPO_ROOT/rtl/common/filelists/common_all.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_all.f
