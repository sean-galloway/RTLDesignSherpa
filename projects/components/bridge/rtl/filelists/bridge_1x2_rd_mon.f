# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_mon/bridge_1x2_rd_mon_pkg.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_mon/cpu_rd_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_mon/bridge_1x2_rd_mon.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_mon/bridge_1x2_rd_mon_xbar.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_mon/ddr_rd_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_mon/sram_rd_adapter.sv

# AXI4 Wrapper modules (timing isolation)
# Master adapters use axi4_slave_* (act as AXI slave to external master)
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv
# Slave adapters use axi4_master_* (act as AXI master to external slave)
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv

# GAXI skid buffers (used by wrappers and converters)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Width converters (for data width adaptation).
# axi_data_{upsize,dnsize} are validated primitives used by the
# axi4_dwidth_converter_{rd,wr} wrappers for the W/R data path.
$REPO_ROOT/projects/components/converters/rtl/axi_data_upsize.sv
$REPO_ROOT/projects/components/converters/rtl/axi_data_dnsize.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv

# Monitor-aggregation infrastructure (variant=mon)
# Header files with macros (already compiled if AMBA pkg path included)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh
# Monitor packages -- must precede module compilation
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
# Common arbitration primitives (used by axi_monitor_*)
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
# Common counters & FIFO control (used by gaxi_fifo_sync + axi_monitor_timer)
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/counter_load_clear.sv
$REPO_ROOT/rtl/common/counter_freq_invariant.sv
$REPO_ROOT/rtl/common/fifo_control.sv
# axi_monitor_* shared infrastructure (order matters)
$REPO_ROOT/rtl/amba/shared/axi_monitor_trans_mgr.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timer.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timeout.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_base.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_filtered.sv
# _mon wrapper variants (instantiated by adapters when use_monitor=true)
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon.sv
# Monbus aggregator + AXIL group
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr.sv
$REPO_ROOT/projects/components/stream/rtl/macro/monbus_axil_group.sv