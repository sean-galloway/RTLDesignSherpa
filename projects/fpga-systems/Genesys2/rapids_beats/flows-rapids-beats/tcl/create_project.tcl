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

# Board target selection (env BOARD=nexys|genesys2; default nexys). The genesys2
# target is the Kintex-7 325T-2 (~3.2x LUTs, faster grade) whose wrapper top
# derives 100 MHz from the 200 MHz LVDS sysclk via an MMCM; everything else is
# shared with the Nexys build.
set part_name      "xc7a100tcsg324-1"
set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
set top_name       "rapids_char_top"
set top_flist_name "rapids_char_top.f"
set xdc_name       "rapids_char_top.xdc"
set board_label    "Nexys A7-100T (xc7a100t-1)"
if {[info exists ::env(BOARD)] && $::env(BOARD) eq "genesys2"} {
    set part_name      "xc7k325tffg900-2"
    set board_part_str "digilentinc.com:genesys2:part0:1.1"
    set top_name       "rapids_char_genesys2_top"
    set top_flist_name "rapids_char_genesys2_top.f"
    set xdc_name       "rapids_char_genesys2_top.xdc"
    set board_label    "Genesys 2 (xc7k325t-2)"
}

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

# Default channel count: the Genesys 2 (Kintex 325T-2) closes the full 8-channel
# geometry with margin; the Nexys A7-100T (-1) is narrowed to 4.
set num_channels 4
if {[info exists ::env(BOARD)] && $::env(BOARD) eq "genesys2"} { set num_channels 8 }
if {[info exists ::env(RAPIDS_NUM_CHANNELS)]} {
    set num_channels $::env(RAPIDS_NUM_CHANNELS)
}

# Board-fit memory sizing. The harness RTL defaults (SRAM_DEPTH=4096,
# DESC_RAM_ENTRIES=2048) are the big ASIC/sim targets and blow past the
# Artix-7 100T's 135 BRAM tiles. A characterization build only needs small
# buffers -- the fmax-limiting paths are control/datapath logic, not memory
# depth -- so we shrink them here (mirrors stream_char's SRAM_DEPTH=256).
# Override via env if a campaign needs deeper buffers and the area allows.
# Datapath design point (Sean, 2026-09-29): 256-bit AXI4 + AXIS (one DATA_WIDTH
# in RAPIDS) and 4 KB of SRAM per channel = 128 beats x 32 B. The Makefile
# exports both (RAPIDS_DATA_WIDTH / RAPIDS_SRAM_DEPTH) and hands the same
# values to verify-sim; these are only the fallbacks for a bare tcl run.
# Perf reports v1.0-v1.5 were measured at 512-bit / 256-deep (16 KB).
set data_width 256
if {[info exists ::env(RAPIDS_DATA_WIDTH)]}       { set data_width $::env(RAPIDS_DATA_WIDTH) }
set sram_depth 128
if {[info exists ::env(RAPIDS_SRAM_DEPTH)]}       { set sram_depth $::env(RAPIDS_SRAM_DEPTH) }
set desc_ram_entries 256
if {[info exists ::env(RAPIDS_DESC_RAM_ENTRIES)]} { set desc_ram_entries $::env(RAPIDS_DESC_RAM_ENTRIES) }

# Extended row/col-major addressing in the DUT (USE_ROW_COL_MAJOR_ADDRESSING).
# Default 0: this build is tuned down to close 8-channel timing and meters
# externally. Set RAPIDS_ROW_COL=1 to measure what the feature costs in area
# and WNS. Threaded top -> char_top -> harness -> rapids_beats_top.
set row_col 0
if {[info exists ::env(RAPIDS_ROW_COL)]} { set row_col $::env(RAPIDS_ROW_COL) }

# In-core monitors + MonBus egress (USE_AXI_MONITORS) and the GEN_MON cone in
# rapids_beats_top. Default 0/0: this build meters externally (axi_bus_meter)
# and is tuned to close 8-channel timing. Set USE_AXI_MONITORS=1 (and GEN_MON=1
# so the packets have an egress and the monitors are not pruned) to measure
# what they cost -- with them compiled out a lite-vs-full monitor comparison is
# unmeasurable. Same knob names STREAM's build-*/Makefile export.
set use_axi_monitors 0
if {[info exists ::env(USE_AXI_MONITORS)]} { set use_axi_monitors $::env(USE_AXI_MONITORS) }
set gen_mon 0
if {[info exists ::env(GEN_MON)]}          { set gen_mon $::env(GEN_MON) }
# Shared interface observers on the harness (axi4_intf_master_observer +
# axis4_intf_observer, rapids TASK-001) and their monbus event taps. Default
# OUT so the characterization bitstream is unchanged; set USE_OBSERVERS=1 to
# measure them, OBS_ENABLE_MON_TAPS=1 to add the taps.
set use_observers 0
if {[info exists ::env(USE_OBSERVERS)]}       { set use_observers $::env(USE_OBSERVERS) }
set obs_enable_mon_taps 0
if {[info exists ::env(OBS_ENABLE_MON_TAPS)]} { set obs_enable_mon_taps $::env(OBS_ENABLE_MON_TAPS) }

puts "========================================================================"
puts "RTL Design Sherpa — RAPIDS beats Characterization ($board_label)"
puts "========================================================================"
puts "Project root:      $project_root"
puts "REPO_ROOT:         $::env(REPO_ROOT)"
puts "Part / top:        $part_name / $top_name"
puts "Row/col addressing: $row_col"
puts "USE_AXI_MONITORS:  $use_axi_monitors"
puts "GEN_MON:           $gen_mon"
puts "USE_OBSERVERS:     $use_observers"
puts "OBS_ENABLE_MON_TAPS: $obs_enable_mon_taps"
puts "NUM_CHANNELS:      $num_channels"
puts "DATA_WIDTH:        $data_width"
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

set top_filelist "$project_root/filelists/$top_flist_name"
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

puts "Setting top module: $top_name"
set_property top $top_name $src_fs

# Narrow the board geometry + memory sizing via top-level generics (see header).
set_property generic "NUM_CHANNELS=$num_channels DATA_WIDTH=$data_width SRAM_DEPTH=$sram_depth DESC_RAM_ENTRIES=$desc_ram_entries USE_ROW_COL_MAJOR_ADDRESSING=$row_col USE_AXI_MONITORS=$use_axi_monitors GEN_MON=$gen_mon USE_OBSERVERS=$use_observers OBS_ENABLE_MON_TAPS=$obs_enable_mon_taps" $src_fs

update_compile_order -fileset sources_1

# ----------------------------------------------------------------------------
# Constraints
# ----------------------------------------------------------------------------
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf \
    "$project_root/constraints/$xdc_name"

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
