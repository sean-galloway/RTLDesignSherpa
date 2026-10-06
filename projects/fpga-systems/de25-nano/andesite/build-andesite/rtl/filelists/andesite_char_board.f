# SYNTHESIS filelist for the andesite board build (de25-nano area,
# Genesys 2 target). This list is what VIVADO reads.
#
# The controller closure is the andesite_core top filelist -- the single
# authority on what the core needs -- plus this build's char top. Unlike the
# scoria build there is NO generated PHY: the DFI 4.0 pins terminate inside
# the top, so nothing here is generated and there is no lint-only
# substitution for synthesis-only content beyond the board top itself.

-f $REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/filelists/top/andesite_core.f

# The board top: andesite_core + the on-chip AXI exerciser.
$REPO_ROOT/projects/fpga-systems/de25-nano/andesite/build-andesite/rtl/andesite_exerciser.sv
$REPO_ROOT/projects/fpga-systems/de25-nano/andesite/build-andesite/rtl/andesite_char_top.sv
