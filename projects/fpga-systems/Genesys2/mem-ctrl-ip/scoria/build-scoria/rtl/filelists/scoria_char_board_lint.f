# LINT filelist for the scoria DDR3 board build.
#
# Two substitutions against the synthesis list, both for the same reason --
# Verilator cannot elaborate Xilinx primitives, and a lint run that reports 50+
# MODMISSING says nothing about this design:
#
#   the PHY        -> rtl/generated/k7ddrphy_bb.sv, a blackbox stub DERIVED
#                     from the generated PHY by bin/gen_core_blackbox.py, so
#                     the interface lint checks is the interface the PHY has.
#                     A hand-written stub of 88 ports would go stale the first
#                     time the PHY was regenerated, and silently: a stale stub
#                     still lints clean.
#   MMCM/BUFG/
#   IBUFDS/
#   IDELAYCTRL     -> the shared verilator_xilinx_stubs.
#
# NEITHER may reach the synthesis list. A stubbed BUFG that survives into a
# build is a clock that is not buffered; a stubbed PHY is a DRAM that is not
# there.
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f
-f $REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/rtl/filelists/scoria_char_harness.f
$REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/rtl/dfi_flat_to_k7ddrphy.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/build-scoria/rtl/generated/k7ddrphy_bb.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/build-scoria/rtl/scoria_char_top.sv
