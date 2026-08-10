# Filelist for axi4_intf_observer
# Location: projects/components/misc/rtl/filelists/axi4_intf_observer.f
#
# The inline AXI-interface observer (pass-through perf meter). It carries its OWN APB config
# regblock (obs_regs) rather than exporting 29 cfg_* ports for whoever
# instantiates it to tie off -- which is what forced each harness to know its
# internals, and is one of the reasons two near-identical stream harnesses
# existed.
#
# Lives in misc/ because it is NOT stream-specific: flows-stream-bridge,
# flows-stream-monitor and flows-idma-bridge all use it, and the blocks it
# wraps (axi_bus_meter, axi_perf_latency_hist) are shared more widely still.
# It was briefly moved into the stream component on the assumption that only
# stream used it; that was wrong.
#
# The pre-migration copy at rtl/amba/shared/axi4_intf_observer.sv still exists
# for the old tree and has no APB -- nothing is deleted until every flow is
# green.

+incdir+$REPO_ROOT/rtl/amba/includes

# Its config regblock + the APB->cmdrsp->passthrough chain behind it.
$REPO_ROOT/projects/components/misc/rtl/regs/obs_regs.vlt
$REPO_ROOT/projects/components/misc/rtl/regs/generated/rtl/obs_regs_top_pkg.sv
$REPO_ROOT/projects/components/misc/rtl/regs/generated/rtl/obs_regs_top.sv
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

# The observer's own dependencies (meters, histogram, monbus arbiter).
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil_axi4_group.f

$REPO_ROOT/projects/components/misc/rtl/axi4_intf_observer.sv
