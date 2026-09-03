# monbus_tally_axil -- AXIL wrapper around monbus_pkt_tally, with its control
# registers in a generated regblock (tally_regs.rdl) rather than hardcoded
# localparam offsets.
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/monbus_pkt_tally.f
$REPO_ROOT/projects/components/misc/rtl/regs/generated/rtl/tally_regs_top_pkg.sv
$REPO_ROOT/projects/components/misc/rtl/regs/generated/rtl/tally_regs_top.sv
$REPO_ROOT/projects/components/misc/rtl/monbus_tally_axil.sv
