#==============================================================================
# create_project.tcl -- Vivado project for the Reed-Solomon loop harness
#==============================================================================
# Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1) [default]
#         Digilent Genesys 2 (xc7k325tffg900-2)      [RS_TARGET=genesys2]
# Top:    rs_loop_top          [RS_TARGET=nexys_a7_100t or unset]
#         rs_loop_genesys2_top [RS_TARGET=genesys2]
# Usage:  run via `make project` / `make bitstream`, which export the layout
#         (FPGA_PROJECT_ROOT / FPGA_BUILD_ROOT / FPGA_FILELIST) and the roots
#         (REPO_ROOT, CONVERTERS_ROOT) this build's filelist resolves against.
#
# Target selection:
#   RS_TARGET=nexys_a7_100t  default; same behavior as before this switch existed
#   RS_TARGET=genesys2       Kintex-7 325T-2 build, 200 MHz LVDS -> 100 MHz MMCM
#==============================================================================

set project_name "rs_loop"
set project_dir  "build/vivado_project"

# Board target selection (env RS_TARGET=nexys_a7_100t|genesys2; default nexys_a7_100t).
# The genesys2 target is the Kintex-7 325T-2 whose wrapper top derives 100 MHz
# from the 200 MHz LVDS sysclk via an MMCM; everything else is shared with the
# Nexys A7 build.
set target "nexys_a7_100t"
if {[info exists ::env(RS_TARGET)]} { set target $::env(RS_TARGET) }

set part_name      "xc7a100tcsg324-1"
set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
set top_name       "rs_loop_top"
set xdc_name       "rs_loop.xdc"
set board_label    "Nexys A7-100T (xc7a100t-1)"
if {$target eq "genesys2"} {
    set part_name      "xc7k325tffg900-2"
    set board_part_str "digilentinc.com:genesys2:part0:1.1"
    set top_name       "rs_loop_genesys2_top"
    set xdc_name       "rs_loop_genesys2.xdc"
    set board_label    "Genesys 2 (xc7k325t-2)"
} elseif {$target ne "nexys_a7_100t"} {
    puts stderr "ERROR: unknown RS_TARGET='$target' (expected nexys_a7_100t or genesys2)"
    exit 1
}

set script_dir   [file dirname [file normalize [info script]]]
# Project root: where Vivado WRITES (build/, reports/, bitstream/) and where
# the constraints live. Falls back to the script-relative guess for direct
# invocation.
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]
# Where the build's SOURCES live (rtl/).
set build_root [expr {[info exists ::env(FPGA_BUILD_ROOT)] \
                      ? [file normalize $::env(FPGA_BUILD_ROOT)] \
                      : [file normalize "$script_dir/../.."]}]

# ----------------------------------------------------------------------------
# Env-var sanity check
# ----------------------------------------------------------------------------
foreach var {REPO_ROOT CONVERTERS_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set."
        puts stderr "Run via the build Makefile (it sets them automatically),"
        puts stderr "or export them manually before invoking vivado."
        exit 1
    }
}

puts "========================================================================"
puts "RTL Design Sherpa -- Reed-Solomon loop harness ($board_label)"
puts "========================================================================"
puts "Project root: $project_root"
puts "Build root:   $build_root"
puts "REPO_ROOT:    $::env(REPO_ROOT)"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"         -objects $obj
set_property -name "simulator_language" -value "Mixed"           -objects $obj

# Optional board-part association -- only if the Digilent board files exist.
if {[lsearch -exact [get_board_parts] $board_part_str] >= 0} {
    set_property board_part $board_part_str [current_project]
}

# ----------------------------------------------------------------------------
# Expand the build filelist into a flat list of sources
# ----------------------------------------------------------------------------
# Shared filelist expander (tooling TASK-019): make/tcl/filelist_utils.tcl.
# REPO_ROOT comes from the Makefile; the git fallback lets the script run by hand.
set rds_root [expr {[info exists ::env(REPO_ROOT)] ? $::env(REPO_ROOT) : [string trim [exec git -C $script_dir rev-parse --show-toplevel]]}]
source "$rds_root/make/tcl/filelist_utils.tcl"

set top_flist_name "${top_name}.f"
set top_filelist [expr {[info exists ::env(FPGA_FILELIST)] \
                        ? [file normalize $::env(FPGA_FILELIST)] \
                        : "$build_root/rtl/filelists/$top_flist_name"}]
puts "\nExpanding filelist: $top_filelist"
if {![file exists $top_filelist]} {
    puts stderr "ERROR: filelist not found: $top_filelist"
    puts stderr "Run via 'make project' / 'make bitstream' (it exports FPGA_FILELIST)."
    exit 1
}
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines

# Drop the verilator-only stubs: Vivado uses the real Xilinx unisims. The stub
# body is `ifdef VERILATOR anyway; excluding the file keeps the empty module
# declarations out of the project entirely.
set filtered {}
foreach src $sv_sources {
    if {[string match "*verilator_xilinx_stubs.sv" $src]} { continue }
    lappend filtered $src
}
set sv_sources $filtered

puts "  [llength $sv_sources] source file(s)"
puts "  [llength $incdirs] include directory(ies)"

# ----------------------------------------------------------------------------
# Add sources / set top
# ----------------------------------------------------------------------------
set src_fs [get_filesets sources_1]
foreach src $sv_sources {
    if {![file exists $src]} {
        puts stderr "ERROR: source not found: $src"
        exit 1
    }
}
add_files -norecurse -fileset $src_fs $sv_sources

foreach src [get_files -of_objects $src_fs -filter {FILE_TYPE == "Verilog"}] {
    if {[string match *.sv $src] || [string match *.svh $src]} {
        set_property FILE_TYPE SystemVerilog $src
    }
}

set_property include_dirs $incdirs $src_fs
if {[llength $defines] > 0} {
    set_property verilog_define $defines $src_fs
}

puts "Setting top module: $top_name"
set_property top $top_name $src_fs
update_compile_order -fileset sources_1

# -----------------------------------------------------------------------------
# Generics: build a flavour other than the RTL defaults.
#
#   RS_IFACE          "AXIS" (default) or "AXI4" -- which datapath
#   RS_ENABLE_COMPARE 1 (default) or 0 -- build decoder B and the comparator
#   RS_KES_ALGO_A     "RIBM" (default) or "EUCLID" -- decoder A's solver
#
# `make lint` is given the SAME values through LINT_GENERICS in the build's
# Makefile. That is deliberate: a lint that runs against the RTL defaults
# while Vivado synthesizes something else cannot catch a
# configuration-specific fault, and this flow has shipped one before.
# -----------------------------------------------------------------------------
# -----------------------------------------------------------------------------
# Implementation effort.
#
# RS_IMPL_STRATEGY names a Vivado run strategy for impl_1; unset means the
# project default. This exists because the stream flavour is ROUTE-bound at the
# margin, not logic-bound: its critical path is the Euclid solver's degree
# register into the descriptor broadcast, 10 logic levels, and at the default
# strategy 78% of its 10.26 ns was routing. Adding the AXIS wrappers' six skid
# buffers grew the design by 495 LUTs and that congestion alone took it from
# +0.269 ns to -0.303 ns with 2 failing endpoints -- the path did not get
# logically longer, it got routed worse.
# -----------------------------------------------------------------------------
# RS_IMPL_EFFORT=explore raises every implementation step's directive and turns
# on post-route physical optimisation. The STEP DIRECTIVES are set explicitly
# rather than by naming a strategy: `set_property strategy
# Performance_ExplorePostRoutePhysOpt` was accepted WITHOUT ERROR and silently
# did not stick -- the project still recorded "Vivado Implementation Defaults"
# and the result was bit-identical to the default run, which is how the no-op
# was caught. Directives are verifiable in the .xpr.
if {[info exists ::env(RS_IMPL_EFFORT)] && $::env(RS_IMPL_EFFORT) eq "explore"} {
    set r [get_runs impl_1]
    set_property STEPS.OPT_DESIGN.ARGS.DIRECTIVE                 Explore $r
    set_property STEPS.PLACE_DESIGN.ARGS.DIRECTIVE               Explore $r
    set_property STEPS.PHYS_OPT_DESIGN.IS_ENABLED                true    $r
    set_property STEPS.PHYS_OPT_DESIGN.ARGS.DIRECTIVE            Explore $r
    set_property STEPS.ROUTE_DESIGN.ARGS.DIRECTIVE               Explore $r
    set_property STEPS.POST_ROUTE_PHYS_OPT_DESIGN.IS_ENABLED     true    $r
    set_property STEPS.POST_ROUTE_PHYS_OPT_DESIGN.ARGS.DIRECTIVE Explore $r
    puts "IMPL EFFORT:  explore (opt/place/phys_opt/route Explore, post-route phys_opt on)"
    puts "IMPL CHECK:   place=[get_property STEPS.PLACE_DESIGN.ARGS.DIRECTIVE $r] route=[get_property STEPS.ROUTE_DESIGN.ARGS.DIRECTIVE $r] post_route_po=[get_property STEPS.POST_ROUTE_PHYS_OPT_DESIGN.IS_ENABLED $r]"
} else {
    puts "IMPL EFFORT:  project default"
}

set rs_generics {}
if {[info exists ::env(RS_IFACE)]} {
    lappend rs_generics "IFACE=\"$::env(RS_IFACE)\""
}
if {[info exists ::env(RS_ENABLE_COMPARE)]} {
    lappend rs_generics "ENABLE_COMPARE=$::env(RS_ENABLE_COMPARE)"
}
if {[info exists ::env(RS_KES_ALGO_A)]} {
    lappend rs_generics "KES_ALGO_A=\"$::env(RS_KES_ALGO_A)\""
}
if {[llength $rs_generics] > 0} {
    set_property generic $rs_generics $src_fs
    puts "GENERICS:     $rs_generics"
} else {
    puts "GENERICS:     none (RTL defaults: IFACE=AXIS, riBM vs Euclid with the comparator)"
}

# ----------------------------------------------------------------------------
# Constraints
# ----------------------------------------------------------------------------
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf "$project_root/constraints/$xdc_name"

# ----------------------------------------------------------------------------
# Strategies -- defaults; this design closes with lots of margin.
# ----------------------------------------------------------------------------
set_property strategy "Vivado Synthesis Defaults"      [get_runs synth_1]
set_property strategy "Vivado Implementation Defaults" [get_runs impl_1]

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
