#==============================================================================
# create_project.tcl -- Vivado project for the Reed-Solomon loop harness
#==============================================================================
# Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1)
# Top:    rs_loop_top
# Usage:  run via `make project` / `make bitstream`, which export the layout
#         (FPGA_PROJECT_ROOT / FPGA_BUILD_ROOT / FPGA_FILELIST) and the roots
#         (REPO_ROOT, CONVERTERS_ROOT) this build's filelist resolves against.
#==============================================================================

set project_name "rs_loop"
set project_dir  "build/vivado_project"
set part_name    "xc7a100tcsg324-1"

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
puts "RTL Design Sherpa -- Reed-Solomon loop harness (Nexys A7-100T)"
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
set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
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

set top_filelist [expr {[info exists ::env(FPGA_FILELIST)] \
                        ? [file normalize $::env(FPGA_FILELIST)] \
                        : "$build_root/rtl/filelists/rs_loop_top.f"}]
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

set_property top rs_loop_top $src_fs
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
add_files -norecurse -fileset $cf "$project_root/constraints/rs_loop.xdc"

# ----------------------------------------------------------------------------
# Strategies -- defaults; this design closes with lots of margin.
# ----------------------------------------------------------------------------
set_property strategy "Vivado Synthesis Defaults"      [get_runs synth_1]
set_property strategy "Vivado Implementation Defaults" [get_runs impl_1]

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
