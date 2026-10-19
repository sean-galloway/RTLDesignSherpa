# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Bridge stress model -- Genesys 2 Vivado project. Run through a build's
# Makefile (build-<dut>/), which sets FLOW, FPGA_FILELIST, FPGA_PROJECT_ROOT
# and, for a DUT other than the AXI4 one, BS_HARNESS.
set script_dir [file dirname [file normalize [info script]]]
set area       [file normalize "$script_dir/../.."]

foreach var {REPO_ROOT FPGA_FILELIST FPGA_PROJECT_ROOT CONVERTERS_ROOT MISC_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set. Run via build-<dut>/Makefile."
        exit 1
    }
}
source "$::env(REPO_ROOT)/make/tcl/filelist_utils.tcl"

set part         xc7k325tffg900-2
set project_root [file normalize $::env(FPGA_PROJECT_ROOT)]
set project_name [expr {[info exists ::env(FLOW)] ? $::env(FLOW) : "bs"}]
set top_name     bs_genesys2_top
set cons_dir     [expr {[info exists ::env(FPGA_CONSTRAINTS_DIR)] \
                        ? $::env(FPGA_CONSTRAINTS_DIR) : "$area/fpga/constraints"}]

puts "========================================================================"
puts "Bridge stress model -- Genesys 2 board build ($project_name)"
puts "  part     $part"
puts "  filelist $::env(FPGA_FILELIST)"
puts "========================================================================"

create_project $project_name "$project_root/build/vivado_project" -part $part -force
set_property target_language Verilog [current_project]

lassign [filelist::flatten $::env(FPGA_FILELIST)] sv_sources incdirs defines
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
if {[info exists ::env(BS_HARNESS)]} { lappend defines "BS_HARNESS=$::env(BS_HARNESS)" }
if {[llength $defines] > 0} { set_property verilog_define $defines $src_fs }

set_property top $top_name $src_fs
update_compile_order -fileset sources_1
add_files -norecurse -fileset [get_filesets constrs_1] [list "$cons_dir/bs_genesys2_top.xdc"]

set impl_run [get_runs impl_1]
set_property strategy "Performance_Explore" $impl_run
set_property steps.phys_opt_design.is_enabled true $impl_run
puts "\nProject created: $project_root/build/vivado_project/${project_name}.xpr"
