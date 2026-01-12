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
#   - Include paths added via command line: -Iincludes -I$REPO_ROOT/rtl/common
#   - Files organized by protocol for maintainability
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
# =============================================================================
$REPO_ROOT/rtl/amba/shared/amba_clock_gate_ctrl.sv
$REPO_ROOT/rtl/amba/shared/arbiter_monbus_common.sv
$REPO_ROOT/rtl/amba/shared/arbiter_rr_pwm_monbus.sv
$REPO_ROOT/rtl/amba/shared/arbiter_wrr_pwm_monbus.sv
$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv
$REPO_ROOT/rtl/amba/shared/axi_master_rd_splitter.sv
$REPO_ROOT/rtl/amba/shared/axi_master_wr_splitter.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_base.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_filtered.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timeout.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timer.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_trans_mgr.sv
$REPO_ROOT/rtl/amba/shared/axi_split_combi.sv
$REPO_ROOT/rtl/amba/shared/cdc_handshake.sv
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv

# =============================================================================
# GAXI - Generic AXI Utilities (FIFOs, Skid Buffers)
# =============================================================================
$REPO_ROOT/rtl/amba/gaxi/gaxi_drop_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_async.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_regslice.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer_async.sv
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

# AXI4 Infrastructure
$REPO_ROOT/rtl/amba/axi4/axi4_interconnect_2x2_mon.sv

# AXI4 Stubs (Test support)
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_master_rd_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_master_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_master_wr_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_rd_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_wr_stub.sv

# AXI4 Future (Under development)
$REPO_ROOT/rtl/amba/axi4/FUTURE/axi4_master_rd_hp_mon.sv
$REPO_ROOT/rtl/amba/axi4/FUTURE/axi4_master_rd_lp_mon.sv

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
# End of filelist
# ==============================================================================
