# Filelist for axis4_intf_observer
# Location: projects/components/utility-ip/misc/rtl/filelists/axis4_intf_observer.f
#
# The AXI4-Stream interface observer: the AXIS sibling of
# axi4_intf_{master,slave}_observer. Same obs_regs regblock behind the same
# APB->cmdrsp->passthrough chain, same monbus arbiter + group egress; the
# per-port event tap is the shared axis_monitor_lite core and the meter is
# the shared axis_bus_meter.

+incdir+$REPO_ROOT/rtl/amba/includes

# Its config regblock + the APB->cmdrsp->passthrough chain behind it.
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/obs_regs.vlt
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/generated/rtl/obs_regs_top_pkg.sv
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/generated/rtl/obs_regs_top.sv
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# The observer's own closure: the CFI tick the taps age with (each
# axis_monitor_lite carries its own counter_freq_invariant driven by the
# same OBS_CTRL.FREQ_SEL_OVR), the AXIS meter, the per-port event taps
# (shared axis_monitor_lite core), the monbus arbiter (which carries the
# monitor packages) and BOTH egress groups -- EGRESS_AXIL is generate-gated,
# so a default-parameter elaboration never reaches the AXIL one and the
# omission would hide until a harness set EGRESS_AXIL(1'b1).
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
-f $REPO_ROOT/rtl/amba/filelists/axis_monitor_lite.f
-f $REPO_ROOT/rtl/amba/filelists/axis_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axil4_group.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axi4_group.f

$REPO_ROOT/projects/components/utility-ip/misc/rtl/axis4_intf_observer.sv
