# Filelist for scoria_char_macro -- the shared char engine behind scoria.
#
# The direct analogue of ddr2_char_macro.f, and deliberately so: it pulls the
# SHARED char_engine_block.f (engine + chargen + generators + perf instruments)
# and swaps only the controller closure. That is what makes a bandwidth number
# from this macro comparable with one from pumice's.
#
# No PHY here. The DFI bus leaves the macro and the sim harness wires it to the
# framework's DFISlavePHY BFM -- which already supports MemoryType.DDR3 and
# decodes ZQCS/ZQCL -- so the whole macro is exercisable in simulation with no
# K7DDRPHY glue at all. That is why the sim harness is the cheaper gate.
#
# ORDER MATTERS. scoria_pkg must precede anything referencing memtype_e. A
# first draft of this file appended the controller closure LAST, after the
# macro, and verilator answered "Reference to 'memtype_e' before declaration"
# -- which reads as a missing package rather than a misordered list.

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# The controller closure FIRST: it carries scoria_pkg.
-f $REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/filelists/top/scoria_top_geared.f

# The shared characterization engine.
-f $REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/filelists/char_engine_block.f

# APB -> PeakRDL cpuif, so the bridge's APB window reaches the controller's
# passthrough register interface. Shared converter, same one pumice uses.
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/apb4_to_peakrdl.f

# The macro itself.
$REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/rtl/scoria_char_macro.sv
