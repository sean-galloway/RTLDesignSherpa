# Filelist for verilator_xilinx_stubs
# Location: projects/components/misc/rtl/filelists/verilator_xilinx_stubs.f
#
# Lint/sim-only pass-through stubs for the Xilinx clocking primitives a board
# top instantiates (BUFG / IBUFDS / MMCME2_BASE). Everything in the file is
# wrapped in `ifdef VERILATOR, so Vivado never sees it and substitutes the real
# unisims at synthesis.
#
# It lives in misc/ rather than in a board area because EVERY board top needs
# the same three primitives: a copy per flow is a copy per flow to drift. Board
# flows -f include this list; see [[flow-layout]].
#
# Leaf module set, no dependencies.

$REPO_ROOT/projects/components/misc/rtl/verilator_xilinx_stubs.sv
