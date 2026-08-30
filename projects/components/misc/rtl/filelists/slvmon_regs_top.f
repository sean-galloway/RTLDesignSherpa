# Filelist for slvmon_regs_top -- the slave-monitor PeakRDL regblock.
#
# This block used to be reachable only through dma_slave_monitors.f. That
# module is gone (it was superseded by axi4_intf_slave_observer, which carries
# its own obs_regs regblock), and deleting its filelist left slvmon_regs_top
# with no filelist at all -- bin/filelist_registry.py --check went FAIL with
# "uncovered module: slvmon_regs_top".
#
# The block itself is NOT dead and must not be deleted with its old parent:
# the Genesys 2 stream monitor build still wires it, via
#   projects/fpga-systems/Genesys2/stream/rtl/bridges/configs/bridge_stream_mon_axil.toml
#   projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/*/slvmon_apb_adapter.sv
#   projects/fpga-systems/Genesys2/stream/bin/slvmon_device.py
#   projects/fpga-systems/Genesys2/stream/build-mon/host/host_reg_walk.py
# and that build is mid-transition onto the observers. So it gets its own
# filelist here rather than being carried by a module that no longer exists.
#
# Regenerate the RTL below with bin/peakrdl_generate.py (never raw
# `peakrdl regblock` -- the wrapper emits RTL + docs + regmap in lockstep)
# from projects/components/misc/rtl/slvmon_regs.rdl.

$REPO_ROOT/projects/components/misc/rtl/regs/slvmon_regs.vlt
$REPO_ROOT/projects/components/misc/rtl/regs/generated/rtl/slvmon_regs_top_pkg.sv
$REPO_ROOT/projects/components/misc/rtl/regs/generated/rtl/slvmon_regs_top.sv
