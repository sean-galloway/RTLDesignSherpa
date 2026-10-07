# LINT filelist for the andesite board build (de25-nano area, Genesys 2
# target). One substitution against the synthesis list, for the reason
# build-scoria's lint list documents: the board top instantiates Xilinx
# primitives (IBUFDS, MMCME2_BASE, BUFG) that Verilator cannot elaborate,
# and a lint run that reports MODMISSING says nothing about this design.
#
# The shared verilator_xilinx_stubs are simulation-only stand-ins and must
# NEVER reach the synthesis list -- a stubbed BUFG that survives into a
# build is a clock that is not buffered.
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/filelists/top/andesite_core.f
$REPO_ROOT/projects/fpga-systems/de25-nano/mem-ctrl-ip/andesite/build-andesite/rtl/andesite_exerciser.sv
$REPO_ROOT/projects/fpga-systems/de25-nano/mem-ctrl-ip/andesite/build-andesite/rtl/andesite_char_top.sv
