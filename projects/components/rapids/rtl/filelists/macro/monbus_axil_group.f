# RAPIDS MonBus AXI-Lite Group Macro File List
# Description: Aggregates monitor bus streams with filtering and AXI-Lite interfaces

# Include directories
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes

# Package files (MUST be first)
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

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/rapids_macro/monbus_axil_group.sv
