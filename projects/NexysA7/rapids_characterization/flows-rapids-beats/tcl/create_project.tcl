#==============================================================================
# create_project.tcl — Vivado project for RAPIDS beats Characterization
#==============================================================================
# Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1)
# Top:    rapids_char_top
# Usage:  REPO_ROOT=... vivado -mode batch -source create_project.tcl
#
# The rapids_char_top.f filelist references only $REPO_ROOT, so this flow needs
# just that one env var (unlike stream_char, whose filelist fans out into
# several component-root vars). Everything else is derived from the script dir.
#
# Optional env:
#   RAPIDS_NUM_CHANNELS  override the top-level NUM_CHANNELS generic (default 4).
#     The RAPIDS beats DUT is 512-bit / 256-bit-descriptor and area-heavy, so the
#     board build narrows the harness geometry to fit the 100T. The default here
#     is 4 (vs the RTL default of 8) mirroring stream_char's overridable approach.
#     IMPORTANT: the host campaign (run_characterization.py --channels N) MUST be
#     told the same N as the bitstream was built with.
#==============================================================================

set project_name "rapids_char"
set project_dir  "build/vivado_project"
set part_name    "xc7a100tcsg324-1"

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

# ----------------------------------------------------------------------------
# Env-var sanity check — only REPO_ROOT is required.
# ----------------------------------------------------------------------------
if {![info exists ::env(REPO_ROOT)]} {
    puts stderr "ERROR: environment variable REPO_ROOT is not set."
    puts stderr "Source the repo's env file (env_python) or export REPO_ROOT"
    puts stderr "before invoking vivado."
    exit 1
}

set num_channels 4
if {[info exists ::env(RAPIDS_NUM_CHANNELS)]} {
    set num_channels $::env(RAPIDS_NUM_CHANNELS)
}

# Board-fit memory sizing. The harness RTL defaults (SRAM_DEPTH=4096,
# DESC_RAM_ENTRIES=2048) are the big ASIC/sim targets and blow past the
# Artix-7 100T's 135 BRAM tiles. A characterization build only needs small
# buffers -- the fmax-limiting paths are control/datapath logic, not memory
# depth -- so we shrink them here (mirrors stream_char's SRAM_DEPTH=256).
# Override via env if a campaign needs deeper buffers and the area allows.
set sram_depth 256
if {[info exists ::env(RAPIDS_SRAM_DEPTH)]}       { set sram_depth $::env(RAPIDS_SRAM_DEPTH) }
set desc_ram_entries 256
if {[info exists ::env(RAPIDS_DESC_RAM_ENTRIES)]} { set desc_ram_entries $::env(RAPIDS_DESC_RAM_ENTRIES) }

puts "========================================================================"
puts "RTL Design Sherpa — RAPIDS beats Characterization (Nexys A7-100T)"
puts "========================================================================"
puts "Project root:      $project_root"
puts "REPO_ROOT:         $::env(REPO_ROOT)"
puts "NUM_CHANNELS:      $num_channels"
puts "SRAM_DEPTH:        $sram_depth"
puts "DESC_RAM_ENTRIES:  $desc_ram_entries"
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

set top_filelist "$project_root/flists/rapids_char_top.f"
puts "\nExpanding filelist: $top_filelist"
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines

puts "  [llength $sv_sources] source file(s)"
puts "  [llength $incdirs] include directory(ies)"
puts "  [llength $defines] macro define(s)"

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
# Single add_files call — much faster than one-at-a-time for many files.
add_files -norecurse -fileset $src_fs $sv_sources

# Flag SystemVerilog where needed (Vivado relies on file extension, but be
# explicit for any file with ambiguous extensions).
foreach src [get_files -of_objects $src_fs -filter {FILE_TYPE == "Verilog"}] {
    if {[string match *.sv $src] || [string match *.svh $src]} {
        set_property FILE_TYPE SystemVerilog $src
    }
}

# Include directories
set_property include_dirs $incdirs $src_fs

# Verilog defines (if the filelist provides any)
if {[llength $defines] > 0} {
    set_property verilog_define $defines $src_fs
}

set top_name rapids_char_top
puts "Setting top module: $top_name"
set_property top $top_name $src_fs

# Narrow the board geometry + memory sizing via top-level generics (see header).
set_property generic "NUM_CHANNELS=$num_channels SRAM_DEPTH=$sram_depth DESC_RAM_ENTRIES=$desc_ram_entries" $src_fs

update_compile_order -fileset sources_1

# ----------------------------------------------------------------------------
# Constraints
# ----------------------------------------------------------------------------
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf \
    "$project_root/constraints/rapids_char_top.xdc"

# ----------------------------------------------------------------------------
# Synthesis / implementation strategy
#
# RAPIDS beats is heavier than stream_char (512-bit datapath, 256-bit
# descriptors), so implementation leans on physical optimization for closure.
# Mirrors the stream_char strategy; tune if the 100T needs more headroom.
# ----------------------------------------------------------------------------
set synth_run [get_runs synth_1]
set_property strategy "Vivado Synthesis Defaults" $synth_run

set impl_run [get_runs impl_1]
set_property strategy "Performance_Explore" $impl_run
set_property steps.phys_opt_design.is_enabled true $impl_run

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
puts "Next:  source $script_dir/build_all.tcl"
