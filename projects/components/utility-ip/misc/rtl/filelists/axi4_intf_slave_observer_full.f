# Full-feature passive AXI slave observer
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/utility-ip/misc/rtl

$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/obs_regs.vlt
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/generated/rtl/obs_regs_top_pkg.sv
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/generated/rtl/obs_regs_top.sv
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_rd_monfull_snoop.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_wr_monfull_snoop.f
-f $REPO_ROOT/rtl/amba/filelists/axi_perf_latency_hist.f
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axil4_group.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axi4_group.f

$REPO_ROOT/projects/components/utility-ip/misc/rtl/axi4_intf_slave_observer_core.sv
$REPO_ROOT/projects/components/utility-ip/misc/rtl/axi4_intf_slave_observer_full.sv
