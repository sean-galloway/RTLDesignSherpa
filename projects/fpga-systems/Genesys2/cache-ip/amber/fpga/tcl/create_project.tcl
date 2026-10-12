#==============================================================================
# create_project.tcl -- Vivado project for the amber pair-rig Genesys2 build
#==============================================================================
# Board:  Digilent Genesys 2 (Kintex-7 xc7k325tffg900-2)
# Top:    amber_pair_genesys2_top
# Usage:  REPO_ROOT=... AMBER_ROOT=... CACHE_COMMON_ROOT=... \
#         CONVERTERS_ROOT=... MISC_ROOT=... make project
#==============================================================================

set project_name "amber"
set project_dir  "build/vivado_project"

set part_name      "xc7k325tffg900-2"
set board_part_str "digilentinc.com:genesys2:part0:1.1"
set top_name       "amber_pair_genesys2_top"
set top_flist_name "amber_pair_genesys2_top.f"
set xdc_name       "amber_pair_genesys2_top.xdc"
set board_label    "Genesys 2 (xc7k325t-2)"

set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]
set build_root   [expr {[info exists ::env(FPGA_BUILD_ROOT)] \
                        ? [file normalize $::env(FPGA_BUILD_ROOT)] \
                        : [file normalize "$script_dir/../.."]}]

foreach var {REPO_ROOT AMBER_ROOT CACHE_COMMON_ROOT CONVERTERS_ROOT MISC_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set. Run via the Makefile."
        exit 1
    }
}

puts "========================================================================"
puts "RTL Design Sherpa -- amber pair-rig Genesys2 bring-up ($board_label)"
puts "========================================================================"
puts "Project root:     $project_root"
puts "Build root:       $build_root"
puts "Part / top:       $part_name / $top_name"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"        -objects $obj
set_property -name "simulator_language" -value "Mixed"          -objects $obj

if {[lsearch -exact [get_board_parts] $board_part_str] >= 0} {
    set_property board_part $board_part_str [current_project]
    puts "Board-part set: $board_part_str"
} else {
    puts "NOTE: board-part '$board_part_str' not available -- skipping."
}

# ---- Expand the top-level filelist ----
set rds_root [expr {[info exists ::env(REPO_ROOT)] ? $::env(REPO_ROOT) : [string trim [exec git -C $script_dir rev-parse --show-toplevel]]}]
source "$rds_root/make/tcl/filelist_utils.tcl"
set top_filelist [expr {[info exists ::env(FPGA_FILELIST)] \
                        ? [file normalize $::env(FPGA_FILELIST)] \
                        : "$build_root/rtl/filelists/$top_flist_name"}]
puts "\nExpanding filelist: $top_filelist"
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines
puts "  [llength $sv_sources] source(s), [llength $incdirs] incdir(s), [llength $defines] define(s)"

set src_fs [get_filesets sources_1]
foreach src $sv_sources {
    if {![file exists $src]} { puts stderr "ERROR: source not found: $src"; exit 1 }
}
add_files -norecurse -fileset $src_fs $sv_sources
foreach src [get_files -of_objects $src_fs -filter {FILE_TYPE == "Verilog"}] {
    if {[string match *.sv $src] || [string match *.svh $src]} {
        set_property FILE_TYPE SystemVerilog $src
    }
}
set_property include_dirs $incdirs $src_fs
if {[llength $defines] > 0} { set_property verilog_define $defines $src_fs }

puts "Setting top module: $top_name"
set_property top $top_name $src_fs
update_compile_order -fileset sources_1

# ---- Constraints ----
set cf [get_filesets constrs_1]
set cons_dir [expr {[info exists ::env(FPGA_CONSTRAINTS_DIR)] \
                        ? $::env(FPGA_CONSTRAINTS_DIR) \
                        : "$project_root/constraints"}]
add_files -norecurse -fileset $cf "$cons_dir/$xdc_name"

# ---- Strategies ----
set_property strategy "Vivado Synthesis Defaults" [get_runs synth_1]
set impl_run [get_runs impl_1]
set_property strategy "Performance_Explore" $impl_run
set_property steps.phys_opt_design.is_enabled true $impl_run

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
