# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Monitor packages (must precede any module that references them)
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

# Bridge RTL files (generated)
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_axi5n_mon/bridge_1x2_rd_axi5n_mon_pkg.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_axi5n_mon/cpu_rd_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_axi5n_mon/bridge_1x2_rd_axi5n_mon.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_axi5n_mon/bridge_1x2_rd_axi5n_mon_xbar.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_axi5n_mon/ddr_rd_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd_axi5n_mon/sram_rd_adapter.sv

# AXI4 Wrapper modules (timing isolation)
#
# Pulled in via each component's OWN filelist rather than by hand-listing
# individual rtl/amba or rtl/common sources. A consumer that hand-lists a
# component's files has to track that component's internal dependencies,
# and it silently rots when they change. Each filelist below declares its
# own complete closure (packages + rtl/common deps + sub-blocks).
# Master adapters use axi4_slave_* (act as AXI slave to external master)
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
# Slave adapters use axi4_master_* (act as AXI master to external slave)
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd.f

# AXI5 boundary wrappers (masters with protocol=axi5).
# Dependency closure: gaxi_skid_buffer only (see gaxi filelist below).
$REPO_ROOT/rtl/amba/axi5/axi5_slave_wr.sv
$REPO_ROOT/rtl/amba/axi5/axi5_slave_rd.sv

# AXI5 boundary wrappers (slaves with protocol=axi5).
# Dependency closure: gaxi_skid_buffer only (see gaxi filelist below).
$REPO_ROOT/rtl/amba/axi5/axi5_master_wr.sv
$REPO_ROOT/rtl/amba/axi5/axi5_master_rd.sv

# GAXI skid buffers (used by wrappers and converters)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

# Width converters (for data width adaptation).
# axi_data_{upsize,dnsize} are validated primitives used by the
# axi4_dwidth_converter_{rd,wr} wrappers for the W/R data path.
#
# -f the converters component's own filelists rather than naming its
# .sv files: a consumer that hand-lists another component's sources has
# to track that component's internal dependencies, and rots silently
# when they change.
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi_data_upsize.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi_data_dnsize.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_converter_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_converter_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil_to_axi4_wide_align_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil_to_axi4_wide_align_rd.f

# Monitor-aggregation infrastructure (variant=mon)
#
# The four _mon wrapper filelists below each declare their OWN complete
# closure: the monitor packages, the shared axi_monitor_* core (base,
# filtered, trans_mgr, timer, timeout and all six reporter sub-blocks),
# monitor_trans_cam, and the rtl/common counters, fifo_control and
# arbiter primitives they depend on. Listing those internals here
# instead would mean tracking another component's guts -- exactly the
# coupling that let the reporter sub-blocks and monitor_trans_cam go
# missing from consumer filelists in the first place.
# _mon wrapper variants (instantiated by adapters when use_monitor=true)
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_mon.f
# AXI5 _mon wrappers (masters with protocol=axi5)
-f $REPO_ROOT/rtl/amba/filelists/axi5_slave_wr_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi5_slave_rd_mon.f
# AXI5 _mon wrappers (slaves with protocol=axi5)
-f $REPO_ROOT/rtl/amba/filelists/axi5_master_wr_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi5_master_rd_mon.f
# Monbus arbiter (always present in mon variant)
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
# Monbus group (monbus_axil_axil_group)
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil_axil_group.f