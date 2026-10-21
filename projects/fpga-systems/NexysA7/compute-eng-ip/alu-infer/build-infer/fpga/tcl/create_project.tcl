#==============================================================================
# create_project.tcl -- Vivado project for the alu-infer harness (Nexys A7-100T)
#==============================================================================
# Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1)
# Top:    alu_nexysa7_top, generic PROFILE from ALU_PROFILE (lean | full)
# Usage:  run via `make project` / `make synth` / `make bitstream`, which
#         export the layout (FPGA_PROJECT_ROOT / FPGA_BUILD_ROOT /
#         FPGA_FILELIST / ALU_REPORTS) and the roots (REPO_ROOT,
#         CONVERTERS_ROOT) this build's filelist resolves against.
#         Modeled on the BCH loop harness's create_project.tcl.
#==============================================================================

set project_name "alu_infer"
set project_dir  "build/vivado_project"
set part_name      "xc7a100tcsg324-1"
set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
set top_name       "alu_nexysa7_top"
set xdc_name       "alu_nexysa7.xdc"

set profile "full"
if {[info exists ::env(ALU_PROFILE)]} { set profile $::env(ALU_PROFILE) }
if {$profile ne "lean" && $profile ne "full"} {
    puts stderr "ERROR: unknown ALU_PROFILE='$profile' (expected lean or full)"
    exit 1
}

set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]
set build_root [expr {[info exists ::env(FPGA_BUILD_ROOT)] \
                      ? [file normalize $::env(FPGA_BUILD_ROOT)] \
                      : [file normalize "$script_dir/../.."]}]
set rpt_dir [expr {[info exists ::env(ALU_REPORTS)] \
                   ? [file normalize $::env(ALU_REPORTS)] \
                   : "$project_root/reports/$profile"}]

foreach var {REPO_ROOT CONVERTERS_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set."
        puts stderr "Run via the build Makefile (it sets them automatically)."
        exit 1
    }
}

puts "========================================================================"
puts "RTL Design Sherpa -- alu-infer harness, Nexys A7-100T, profile $profile"
puts "========================================================================"
puts "Project root: $project_root"
puts "Build root:   $build_root"
puts "Reports:      $rpt_dir"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"         -objects $obj
set_property -name "simulator_language" -value "Mixed"           -objects $obj
if {[lsearch -exact [get_board_parts] $board_part_str] >= 0} {
    set_property board_part $board_part_str [current_project]
}

# ----------------------------------------------------------------------------
# Expand the build filelist (shared expander, make/tcl/filelist_utils.tcl)
# ----------------------------------------------------------------------------
set rds_root [expr {[info exists ::env(REPO_ROOT)] ? $::env(REPO_ROOT) : [string trim [exec git -C $script_dir rev-parse --show-toplevel]]}]
source "$rds_root/make/tcl/filelist_utils.tcl"

set top_filelist [expr {[info exists ::env(FPGA_FILELIST)] \
                        ? [file normalize $::env(FPGA_FILELIST)] \
                        : "$build_root/rtl/filelists/${top_name}.f"}]
if {![file exists $top_filelist]} {
    puts stderr "ERROR: filelist not found: $top_filelist"
    exit 1
}
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines

set filtered {}
foreach src $sv_sources {
    if {[string match "*verilator_xilinx_stubs.sv" $src]} { continue }
    lappend filtered $src
}
set sv_sources $filtered
puts "  [llength $sv_sources] source file(s), [llength $incdirs] include dir(s)"

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
set_property top $top_name $src_fs
update_compile_order -fileset sources_1

# The profile generic. `make lint` gets the SAME value via LINT_GENERICS.
set_property generic "PROFILE=\"[string toupper $profile]\"" $src_fs
puts "GENERICS:     PROFILE=[string toupper $profile]"

set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf "$project_root/constraints/$xdc_name"

set_property strategy "Vivado Synthesis Defaults"      [get_runs synth_1]
set_property strategy "Vivado Implementation Defaults" [get_runs impl_1]

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
