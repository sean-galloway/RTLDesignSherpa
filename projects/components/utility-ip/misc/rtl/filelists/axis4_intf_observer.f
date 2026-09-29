# Filelist for axis4_intf_observer
# Location: projects/components/utility-ip/misc/rtl/filelists/axis4_intf_observer.f
#
# The inline AXI4-Stream interface observer: the AXIS sibling of
# axi4_intf_{master,slave}_observer. Same obs_regs regblock behind the same
# APB->cmdrsp->passthrough chain, same monbus arbiter + group egress; the
# per-port event tap is written in the module itself (no axis4_* monitor
# exists in rtl/amba/monitor to wrap) and the meter is the shared
# axis_bus_meter.

+incdir+$REPO_ROOT/rtl/amba/includes

# Its config regblock + the APB->cmdrsp->passthrough chain behind it.
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/obs_regs.vlt
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/generated/rtl/obs_regs_top_pkg.sv
$REPO_ROOT/projects/components/utility-ip/misc/rtl/regs/generated/rtl/obs_regs_top.sv
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# The observer's own closure: the microsecond tick MON_TIMEOUT is expressed
# in, the AXIS meter, the monbus arbiter (which carries the monitor packages)
# and BOTH egress groups -- EGRESS_AXIL is generate-gated, so a
# default-parameter elaboration never reaches the AXIL one and the omission
# would hide until a harness set EGRESS_AXIL(1'b1).
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
-f $REPO_ROOT/rtl/amba/filelists/axis_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axil4_group.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axi4_group.f

$REPO_ROOT/projects/components/utility-ip/misc/rtl/axis4_intf_observer.sv
