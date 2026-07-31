#==============================================================================
# create_project.tcl — Vivado project for DDR2/LPDDR2 Characterization
#==============================================================================
# Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1)
# Top:    ddr2_char_top
# Usage:  REPO_ROOT=... CONVERTERS_ROOT=... vivado -mode batch -source \
#         create_project.tcl
# The Makefile sets these env vars for you.
#==============================================================================

set project_name "ddr2_char"
set project_dir  "build/vivado_project"
set part_name    "xc7a100tcsg324-1"

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

# ----------------------------------------------------------------------------
# Env-var sanity check
# ----------------------------------------------------------------------------
foreach var {REPO_ROOT CONVERTERS_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set."
        puts stderr "Run via the project Makefile (it sets them automatically),"
        puts stderr "or export them manually before invoking vivado."
        exit 1
    }
}

puts "========================================================================"
puts "RTL Design Sherpa — DDR2/LPDDR2 Characterization (Nexys A7-100T)"
puts "========================================================================"
puts "Project root:     $project_root"
puts "REPO_ROOT:        $::env(REPO_ROOT)"
puts "CONVERTERS_ROOT:  $::env(CONVERTERS_ROOT)"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"         -objects $obj
set_property -name "simulator_language" -value "Mixed"           -objects $obj

# Optional board-part association — only applied if the Digilent board files
# are installed. Not required for synthesis/impl since the part is already set
# and the XDC handles all pin mapping.
set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
if {[lsearch -exact [get_board_parts] $board_part_str] >= 0} {
    set_property board_part $board_part_str [current_project]
    puts "Board-part set: $board_part_str"
} else {
    puts "NOTE: board-part '$board_part_str' not available — skipping."
    puts "      (Install Digilent board files to enable; not required for build.)"
}

# ----------------------------------------------------------------------------
# Expand the top-level filelist into a flat list of Verilog sources.
# ----------------------------------------------------------------------------
source "$script_dir/filelist_utils.tcl"

set top_filelist "$project_root/rtl/filelists/ddr2_char_harness.f"
puts "\nExpanding filelist: $top_filelist"
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines

puts "  [llength $sv_sources] source file(s)"
puts "  [llength $incdirs] include directory(ies)"
puts "  [llength $defines] macro define(s)"

# Filter out verilator-only stubs (BUFG pass-through etc). Vivado uses the
# real Xilinx primitives; the stub is guarded by `ifdef VERILATOR` but we
# also drop the file from the fileset so Vivado never sees the empty
# module declaration.
set filtered {}
foreach src $sv_sources {
    if {[string match "*verilator_xilinx_stubs.sv" $src]} { continue }
    # a7ddrphy_stub.sv is the sim-only black-box declaration. Vivado needs
    # the REAL LiteDRAM-generated body (OSERDESE2/ISERDESE2/IDELAYE2 stack).
    # Drop the stub and substitute a7ddrphy_generated.v below.
    if {[string match "*a7ddrphy_stub.sv" $src]} { continue }
    lappend filtered $src
}
# Real generated PHY (regenerate via bin/elaborate_a7ddrphy.py; see
# bin/README_a7ddrphy.md). Same module name `a7ddrphy` as the stub.
set a7ddrphy_gen "$project_root/rtl-vivado/a7ddrphy/a7ddrphy_generated.v"
if {![file exists $a7ddrphy_gen]} {
    puts stderr "ERROR: generated a7ddrphy not found: $a7ddrphy_gen"
    puts stderr "Generate it first (bin/README_a7ddrphy.md)."
    exit 1
}
lappend filtered $a7ddrphy_gen
set sv_sources $filtered

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

# Use the async-reset variant of the reset macros — the harness has an
# async-reset synchroniser at the boundary and the internal flops all use
# FDCE/FDPE. Matches the +define+USE_ASYNC_RESET the verilator lint uses.
set current_defines [get_property verilog_define $src_fs]
lappend current_defines "USE_ASYNC_RESET"
# DDR2_CHAR_SYNTH selects the real MMCME2_BASE / BUFG / IDELAYCTRL clocking
# in ddr2_char_top (sim path aliases all clocks to CLK100MHZ instead).
lappend current_defines "DDR2_CHAR_SYNTH"
set_property verilog_define $current_defines $src_fs

set top_name ddr2_char_top
puts "Setting top module: $top_name"
set_property top $top_name $src_fs
update_compile_order -fileset sources_1

# ----------------------------------------------------------------------------
# Constraints
# ----------------------------------------------------------------------------
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf \
    "$project_root/constraints/ddr2_char_top.xdc"

# ----------------------------------------------------------------------------
# Synthesis / implementation strategy
#
# Start with the same strategy stream_characterization ended up needing to
# close 100 MHz on the -1 speed grade. Cheap insurance: if we close with
# margin to spare on default, we can dial back later; if we need more
# headroom, we already have the levers pulled.
# ----------------------------------------------------------------------------
set synth_run [get_runs synth_1]
set_property strategy "Vivado Synthesis Defaults" $synth_run

set impl_run [get_runs impl_1]
set_property strategy "Performance_Explore" $impl_run
set_property steps.phys_opt_design.is_enabled true $impl_run

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
puts "Next:  source $script_dir/build_all.tcl"
