# Filelist for cxs_intf_observer
# Location: projects/components/utility-ip/misc/rtl/filelists/cxs_intf_observer.f
#
# The CXS link observer: the CXS sibling of axis4_intf_observer. Same
# obs_regs regblock behind the same APB->cmdrsp->passthrough chain, same
# monbus arbiter + group egress; per port a cxs_link_snoop feeds the shared
# cxs_monitor_lite core, and the meter is the shared axis_bus_meter.

+incdir+$REPO_ROOT/rtl/amba/includes

# Its config regblock + the APB->cmdrsp->passthrough chain behind it.
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/obs_regs.vlt
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/generated/rtl/obs_regs_top_pkg.sv
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/generated/rtl/obs_regs_top.sv
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# Both egress groups: EGRESS_AXIL is generate-gated (see axis4_intf_observer.f).
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
-f $REPO_ROOT/rtl/amba/filelists/cxs_link_snoop.f
-f $REPO_ROOT/rtl/amba/filelists/cxs_monitor_lite.f
-f $REPO_ROOT/rtl/amba/filelists/axis_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axil4_group.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axi4_group.f

$REPO_ROOT/projects/components/utility-ip/misc/rtl/cxs_intf_observer.sv
