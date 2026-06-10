# RAPIDS MonBus AXI-Lite Group Macro File List
# Description: Aggregates monitor bus streams with filtering and AXI-Lite interfaces

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

# Monitor bus arbiter
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv

# GAXI FIFO (used for error and write FIFOs)
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/common/fifo_sync.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/counter_bin.sv

# AXI-Lite slave and master components
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Common utilities
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv

# Compressor (optional; selected by USE_COMPRESSION=1 in the core)
$REPO_ROOT/rtl/amba/shared/monbus_cam.sv
$REPO_ROOT/rtl/amba/shared/monbus_compressor.sv

# Protocol-agnostic core + AXIL/AXIL wrapper (replaces legacy monbus_axil_group.sv).
# Other variants in the monbus_<p1>_<p2>_group family live alongside:
#   monbus_axil_axi4_group.sv, monbus_axi4_axil_group.sv, monbus_axi4_axi4_group.sv
$REPO_ROOT/rtl/amba/shared/monbus_group_core.sv
$REPO_ROOT/rtl/amba/shared/monbus_axil_axil_group.sv

# RAPIDS 2-input wrapper: monbus_arbiter(2) + the shared AXIL/AXIL group
$REPO_ROOT/projects/components/rapids/rtl/macro/monbus_axil_group_2in.sv
