#==============================================================================
# synth_area_dma.tcl — out-of-context area synthesis of the BARE STREAM DMA
#==============================================================================
# Purpose: produce an apples-to-apples area number for stream_top_ch8 alone,
# for comparison against other scatter-gather DMA cores (vendor / OSS). The
# characterization harness (UART bridge, CSR block, axi4_dma_observer, response-
# delay model, trace SRAM) is deliberately NOT included — those are measurement
# scaffolding, not part of the DMA.
#
# The monitors are NOT part of the datapath — stream_top_ch8 defaults to
# USE_AXI_MONITORS=0, so the descriptor AXI monitor / monbus group are simply
# not instantiated in the default config. The default IS the bare DMA, which is
# exactly what a monitor-less competitor core ships. This script therefore does
# not override any monitor parameter; it only pins the datapath sizing.
#
# The datapath configuration is pinned to the as-built FPGA bitstream
# (stream_char_top.sv): 8 channels, 128-bit data, 32-bit addr, SRAM_DEPTH=256,
# AR/AW_MAX_OUTSTANDING=8, CDC disabled (pclk=aclk on the board build).
#
# Usage (via the Makefile):  make area
#   REPO_ROOT / STREAM_ROOT must be set (the Makefile exports them).
#
# SWEEPING CONFIGS — each config writes its OWN report file, auto-named from the
# config, so successive runs never clobber each other. Override via env vars:
#   AREA_NUM_CHANNELS  (default 8)    AREA_SRAM_DEPTH  (default 256)
#   AREA_DATA_WIDTH    (default 128)
# Examples:
#   make area                       -> ..._8ch_dw128_sd256.txt
#   AREA_NUM_CHANNELS=4 make area   -> ..._4ch_dw128_sd256.txt
#
# Output (per config):  reports/utilization_area_<tag>.txt   (flat + hierarchical)
#                       reports/timing_summary_area_<tag>.txt
#==============================================================================

set part_name  "xc7a100tcsg324-1"
set top_name   "stream_top_ch8"

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set project_dir  "build/vivado_area"

# ----------------------------------------------------------------------------
# Env-var sanity check
# ----------------------------------------------------------------------------
foreach var {REPO_ROOT STREAM_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set."
        puts stderr "Run via the project Makefile (it sets them automatically)."
        exit 1
    }
}

puts "========================================================================"
puts "STREAM bare-DMA area synthesis (out-of-context)"
puts "  Top:   $top_name"
puts "  Part:  $part_name"
puts "========================================================================"

create_project stream_area "$project_root/$project_dir" -part $part_name -force
set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"        -objects $obj
set_property -name "simulator_language" -value "Mixed"          -objects $obj

# ----------------------------------------------------------------------------
# Expand the stream_top_ch8 filelist into a flat source list.
# ----------------------------------------------------------------------------
source "$script_dir/filelist_utils.tcl"

set top_filelist "$::env(STREAM_ROOT)/rtl/filelists/top/stream_top_ch8.f"
puts "\nExpanding filelist: $top_filelist"
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines

# Drop Verilator-only waiver files (*.vlt) — invalid for Vivado.
set vivado_sources {}
foreach src $sv_sources {
    if {[string match *.vlt $src]} { continue }
    if {![file exists $src]} {
        puts stderr "ERROR: source not found: $src"
        exit 1
    }
    lappend vivado_sources $src
}
puts "  [llength $vivado_sources] source file(s), [llength $incdirs] include dir(s)"

# ----------------------------------------------------------------------------
# Monitors are OFF in this build (USE_AXI_MONITORS=0), so the monitor CSRs are
# dead logic. Swap the canonical stream_regs.sv / stream_regs_pkg.sv for their
# read-as-zero (sw=r) variant when the Makefile's regen-regs-nomon target has
# produced them in $STREAM_REGS_NOMON_DIR. The RO variant has the identical
# module name, port list, and address map — only the monitor register storage
# and write-decode are removed — so nothing else in the design changes. This is
# channel-count independent: one RO regs serves every AREA_NUM_CHANNELS.
# ----------------------------------------------------------------------------
if {[info exists ::env(STREAM_REGS_NOMON_DIR)]} {
    set nomon_dir $::env(STREAM_REGS_NOMON_DIR)
    set swapped {}
    set n_swap 0
    foreach src $vivado_sources {
        set base [file tail $src]
        if {$base eq "stream_regs.sv" || $base eq "stream_regs_pkg.sv"} {
            set cand [file join $nomon_dir $base]
            if {[file exists $cand]} {
                puts "  \[nomon\] read-as-zero register map: $base <- $nomon_dir"
                lappend swapped $cand
                incr n_swap
                continue
            }
        }
        lappend swapped $src
    }
    set vivado_sources $swapped
    if {$n_swap == 0} {
        puts "  \[nomon\] WARNING: STREAM_REGS_NOMON_DIR set but no RO regs found — using monitors-ON regs"
    }
}

set src_fs [get_filesets sources_1]
add_files -norecurse -fileset $src_fs $vivado_sources
foreach src [get_files -of_objects $src_fs -filter {FILE_TYPE == "Verilog"}] {
    if {[string match *.sv $src] || [string match *.svh $src]} {
        set_property FILE_TYPE SystemVerilog $src
    }
}
set_property include_dirs $incdirs $src_fs
if {[llength $defines] > 0} {
    set_property verilog_define $defines $src_fs
}

# ----------------------------------------------------------------------------
# Datapath config (env-overridable). Each distinct config self-names its report,
# so a sweep produces one file per config instead of clobbering a single file.
# Defaults pin the datapath to the as-built bitstream.
#
# Monitors are explicitly OFF for the bare-DMA number: USE_AXI_MONITORS=0
# removes the data AND descriptor AXI monitors (base + transaction CAM +
# reporters), and GEN_MON=0 drops the per-channel completion/error MonBus
# emitters. The monitors are an opt-in observability layer, not part of the
# datapath, so they have no place in an SG-DMA area comparison.
# ----------------------------------------------------------------------------
proc env_or {name default} {
    if {[info exists ::env($name)]} { return $::env($name) }
    return $default
}
set num_channels [env_or AREA_NUM_CHANNELS 8]
set data_width   [env_or AREA_DATA_WIDTH   128]
set sram_depth   [env_or AREA_SRAM_DEPTH   256]

set generics [list \
    "NUM_CHANNELS=$num_channels" \
    "DATA_WIDTH=$data_width" \
    "ADDR_WIDTH=32" \
    "SRAM_DEPTH=$sram_depth" \
    "AXI_ID_WIDTH=8" \
    "AXI_USER_WIDTH=3" \
    "APB_ADDR_WIDTH=12" \
    "APB_DATA_WIDTH=32" \
    "CDC_ENABLE=0" \
    "AR_MAX_OUTSTANDING=8" \
    "AW_MAX_OUTSTANDING=8" \
    "USE_AXI_MONITORS=0" \
    "GEN_MON=0" \
]
set_property generic $generics $src_fs

# Per-config report tag, e.g. "8ch_dw128_sd256".
set tag "${num_channels}ch_dw${data_width}_sd${sram_depth}"
puts "  config: $tag  (monitors off by default — USE_AXI_MONITORS=0)"

set_property top $top_name $src_fs
update_compile_order -fileset sources_1

# Out-of-context: no I/O buffers, no top-level clock constraints required.
set_property -name {STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS} \
    -value {-mode out_of_context} -objects [get_runs synth_1]

# ----------------------------------------------------------------------------
# Synthesize and report.
# ----------------------------------------------------------------------------
puts "\n--- Out-of-context synthesis ---"
reset_run synth_1
launch_runs synth_1 -jobs 4
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed. See $project_root/$project_dir for logs."
    exit 1
}

file mkdir "$project_root/reports"
open_run synth_1 -name synth_1

set util_rpt "$project_root/reports/utilization_area_${tag}.txt"
set tim_rpt  "$project_root/reports/timing_summary_area_${tag}.txt"
report_utilization              -file $util_rpt
report_utilization -hierarchical -append -file $util_rpt
report_timing_summary           -file $tim_rpt

puts "========================================================================"
puts "Bare-DMA area synthesis complete — config $tag."
puts "  $util_rpt"
puts "  $tim_rpt"
puts "========================================================================"
