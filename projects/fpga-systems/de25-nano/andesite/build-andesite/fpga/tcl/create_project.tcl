#==============================================================================
# create_project.tcl -- Vivado project for the andesite skeleton on Genesys 2
#==============================================================================
# Board:  Digilent Genesys 2 (xc7k325tffg900-2) -- the timing/build vehicle
#         for the DE25-Nano area until that board lands.
# Top:    andesite_char_top
# Usage:  run via `make bitstream`, which exports the env vars below.
#==============================================================================

set project_name "andesite_ddr4"
set project_dir  "build/vivado_project"
set part_name    "xc7k325tffg900-2"

set script_dir   [file dirname [file normalize [info script]]]
# FPGA_PROJECT_ROOT is where Vivado WRITES (fpga/); FPGA_BUILD_ROOT is where the
# build's SOURCES live (rtl/). They are different directories and were the
# same only under the older flat layout -- a tcl that uses one for both is
# right by accident until the layout splits.
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]
set build_root   [expr {[info exists ::env(FPGA_BUILD_ROOT)] \
                        ? [file normalize $::env(FPGA_BUILD_ROOT)] \
                        : [file normalize "$script_dir/../.."]}]

if {![info exists ::env(REPO_ROOT)]} {
    puts stderr "ERROR: REPO_ROOT is not set. Run via the build Makefile."
    exit 1
}

puts "========================================================================"
puts "RTL Design Sherpa -- andesite skeleton on Genesys 2 (de25-nano area)"
puts "========================================================================"
puts "  No PHY: the DFI 4.0 pins terminate at an observability tree in the"
puts "  top. This build exists to surface Vivado build/timing issues early."
puts "  Project root: $project_root"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"        -objects $obj
set_property -name "simulator_language" -value "Mixed"          -objects $obj

# ---- sources, from the filelist the Makefile already names ------------------
set rds_root [expr {[info exists ::env(REPO_ROOT)] ? $::env(REPO_ROOT) \
                    : [string trim [exec git -C $script_dir rev-parse --show-toplevel]]}]
source "$rds_root/make/tcl/filelist_utils.tcl"

set top_filelist [expr {[info exists ::env(FPGA_FILELIST)] \
                        ? [file normalize $::env(FPGA_FILELIST)] \
                        : "$build_root/rtl/filelists/andesite_char_board.f"}]
puts "\nExpanding filelist: $top_filelist"
if {![file exists $top_filelist]} {
    puts stderr "ERROR: filelist not found: $top_filelist"
    exit 1
}
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines
puts "  [llength $sv_sources] source file(s)"

# Drop Verilator-only files defensively. The synthesis list does not reference
# them, but if one ever lands there it must not reach Vivado: a stubbed BUFG
# that survives into a build is a clock that is not buffered.
set filtered {}
foreach src $sv_sources {
    if {[string match "*verilator_xilinx_stubs.sv" $src]}      { continue }
    lappend filtered $src
}
set sv_sources $filtered

foreach src $sv_sources {
    if {![file exists $src]} {
        puts stderr "ERROR: source not found: $src"
        exit 1
    }
}
set src_fs [get_filesets sources_1]
add_files -norecurse -fileset $src_fs $sv_sources
foreach src [get_files -of_objects $src_fs -filter {FILE_TYPE == "Verilog"}] {
    if {[string match *.sv $src] || [string match *.svh $src]} {
        set_property FILE_TYPE SystemVerilog $src
    }
}
set_property include_dirs $incdirs $src_fs
if {[llength $defines] > 0} { set_property verilog_define $defines $src_fs }

set_property top "andesite_char_top" $src_fs
update_compile_order -fileset sources_1

# ---- constraints -----------------------------------------------------------
# Hand-written only: no generated DDR3 pin file (no PHY) and no core-shipped
# timing XDC (andesite_core carries no constraints of its own yet -- its CDC
# blocks are synchronizers timed by construction, which is a known follow-up
# to audit against the family's false-path discipline).
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf \
    "$project_root/constraints/board_pins.xdc" \
    "$project_root/constraints/timing.xdc"

set_property strategy "Vivado Synthesis Defaults" [get_runs synth_1]
set_property strategy "Performance_Explore"       [get_runs impl_1]
set_property steps.phys_opt_design.is_enabled true [get_runs impl_1]

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
