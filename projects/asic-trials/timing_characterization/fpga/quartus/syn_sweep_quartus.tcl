# ==============================================================================
# syn_sweep_quartus.tcl -- Quartus Prime target-frequency sweep for char_top
# ==============================================================================
# The Quartus twin of `make bitstream-sweep` (Vivado). For every frequency in
# FREQS_MHZ it creates a fresh project, compiles char_top (map -> fit -> sta,
# no assembler), runs sta_reports.tcl for per-FUB slack / data delay / logic
# levels, and archives the summaries under REPORTS_DIR/sweep_<F>MHz/.
#
# Usage (from the timing_characterization root or anywhere -- paths are
# resolved from this script's own location):
#
#   quartus_sh -t fpga/quartus/syn_sweep_quartus.tcl [config.tcl] [-freqs "100 150"] [-dry-run]
#   cd fpga && make quartus-sweep [QUARTUS_CFG=quartus/my_sweep.tcl] [FREQS_MHZ="100 150"]
#
#   config.tcl   plain `set` statements; see sweep_config.example.tcl for
#                every key and its default
#   -freqs       override FREQS_MHZ from the command line
#   -dry-run     print the plan and write the per-point SDC wrappers, but
#                call nothing from Quartus. Runs under plain tclsh, which is
#                how the script's logic is exercised on a machine without
#                Quartus:  tclsh syn_sweep_quartus.tcl sweep_config.example.tcl -dry-run
#
# Then aggregate:
#   python3 fpga/tools/parse_timing_sweep.py --tool quartus fpga/reports/quartus fpga/reports/quartus/sweep_wns.csv
#
# How the constraint reaches the design: each point gets a two-line SDC
# wrapper that sets FLOW "quartus" and TARGET_FREQ_MHZ (plus the I/O
# fractions and uncertainty) and then sources rtl/syn/char_top.sdc -- the same
# multi-flow SDC the ASIC and Vivado flows use, so the three flows measure the
# same constraint. The wrapper is the project's SDC_FILE.
# ==============================================================================

# ---- locate ourselves --------------------------------------------------------
set script_dir [file dirname [file normalize [info script]]]
set flow_root  [file normalize [file join $script_dir ..]]     ;# fpga/
set tc_root    [file normalize [file join $flow_root ..]]      ;# timing_characterization/

# ---- defaults (every key sweep_config.example.tcl documents) -----------------
set FAMILY                "Cyclone V"
set DEVICE                5CGXFC5C6F27C7
set FREQS_MHZ             {100 150 200 250 300}
set TOP                   char_top
set FILELIST              rtl/filelists/char_top.f
set MASTER_SDC            rtl/syn/char_top.sdc
set PARAMETERS            {}
set INPUT_DELAY_FRACTION  0.80
set OUTPUT_DELAY_FRACTION 0.20
set CLK_UNCERTAINTY_NS    0.100
set OPTIMIZATION_MODE     "HIGH PERFORMANCE EFFORT"
set FITTER_SEED           1
set VIRTUAL_PINS          0
set BUILD_DIR             fpga/build/quartus
set REPORTS_DIR           fpga/reports/quartus

# ---- arguments ----------------------------------------------------------------
# quartus_sh -t passes script arguments in $quartus(args); tclsh in $argv.
set args {}
if {[info exists quartus(args)]} { set args $quartus(args) } elseif {[info exists argv]} { set args $argv }
set dry_run 0
set freqs_override {}
set config_file ""
for {set i 0} {$i < [llength $args]} {incr i} {
    set a [lindex $args $i]
    switch -glob -- $a {
        -dry-run { set dry_run 1 }
        -freqs   { incr i; set freqs_override [lindex $args $i] }
        -*       { puts stderr "unknown option '$a'"; exit 2 }
        default  { set config_file $a }
    }
}
if {$config_file ne ""} {
    if {![file exists $config_file]} { puts stderr "config file not found: $config_file"; exit 2 }
    source $config_file
}
if {$freqs_override ne ""} { set FREQS_MHZ $freqs_override }

proc abs_path {p base} {
    if {[file pathtype $p] eq "absolute"} { return [file normalize $p] }
    return [file normalize [file join $base $p]]
}
set FILELIST    [abs_path $FILELIST    $tc_root]
set MASTER_SDC  [abs_path $MASTER_SDC  $tc_root]
set BUILD_DIR   [abs_path $BUILD_DIR   $tc_root]
set REPORTS_DIR [abs_path $REPORTS_DIR $tc_root]
foreach f [list $FILELIST $MASTER_SDC] {
    if {![file exists $f]} { puts stderr "missing: $f"; exit 2 }
}

# ---- sources from the repo-style filelist (same expander as the Vivado flow)
foreach v {REPO_ROOT TIMING_CHAR_ROOT FPGA_FLOW_ROOT} {
    if {![info exists ::env($v)]} {
        switch $v {
            REPO_ROOT        { set ::env($v) [file normalize [file join $tc_root .. .. ..]] }
            TIMING_CHAR_ROOT { set ::env($v) $tc_root }
            FPGA_FLOW_ROOT   { set ::env($v) $flow_root }
        }
    }
}
source [file join $flow_root tcl filelist_utils.tcl]
lassign [filelist::flatten $FILELIST] sources incdirs defines
foreach s $sources {
    if {![file exists $s]} { puts stderr "source listed in $FILELIST is missing: $s"; exit 2 }
}

puts "========================================================================"
puts "Timing Characterization -- Quartus target-frequency sweep"
puts "========================================================================"
puts "FAMILY / DEVICE:   $FAMILY / $DEVICE"
puts "TOP:               $TOP  ([llength $sources] sources, [llength $incdirs] include dirs)"
puts "FREQS_MHZ:         $FREQS_MHZ"
puts "PARAMETERS:        [expr {$PARAMETERS eq {} ? "(RTL defaults)" : $PARAMETERS}]"
puts "I/O split:         in $INPUT_DELAY_FRACTION / out $OUTPUT_DELAY_FRACTION, uncertainty $CLK_UNCERTAINTY_NS ns"
puts "VIRTUAL_PINS:      $VIRTUAL_PINS"
puts "BUILD_DIR:         $BUILD_DIR"
puts "REPORTS_DIR:       $REPORTS_DIR"
if {$dry_run} { puts "MODE:              DRY RUN (no Quartus calls)" }
puts "========================================================================"

# ---- the per-point SDC wrapper ------------------------------------------------
proc write_sdc_wrapper {path freq in_frac out_frac unc master} {
    set fh [open $path w]
    puts $fh "# Auto-generated by syn_sweep_quartus.tcl -- do not hand-edit; the sweep regenerates it."
    puts $fh "set FLOW                  quartus"
    puts $fh "set TARGET_FREQ_MHZ       $freq"
    puts $fh "set INPUT_DELAY_FRACTION  $in_frac"
    puts $fh "set OUTPUT_DELAY_FRACTION $out_frac"
    puts $fh "set CLK_UNCERTAINTY_NS    $unc"
    puts $fh "source \"$master\""
    close $fh
}

# ---- one point: project, compile, reports -------------------------------------
proc run_point {freq point_dir sdc} {
    global FAMILY DEVICE TOP PARAMETERS OPTIMIZATION_MODE FITTER_SEED VIRTUAL_PINS sources incdirs defines script_dir
    load_package flow
    cd $point_dir
    project_new $TOP -overwrite -revision $TOP
    set_global_assignment -name FAMILY $FAMILY
    set_global_assignment -name DEVICE $DEVICE
    set_global_assignment -name TOP_LEVEL_ENTITY $TOP
    set_global_assignment -name PROJECT_OUTPUT_DIRECTORY output_files
    set_global_assignment -name OPTIMIZATION_MODE $OPTIMIZATION_MODE
    set_global_assignment -name SEED $FITTER_SEED
    set_global_assignment -name TIMING_ANALYZER_MULTICORNER_ANALYSIS ON
    set_global_assignment -name SDC_FILE $sdc
    foreach d $incdirs { set_global_assignment -name SEARCH_PATH $d }
    foreach s $sources { set_global_assignment -name SYSTEMVERILOG_FILE $s }
    foreach d $defines { set_global_assignment -name VERILOG_MACRO $d }
    foreach {n v} $PARAMETERS { set_parameter -name $n $v }
    if {$VIRTUAL_PINS} { set_instance_assignment -name VIRTUAL_PIN ON -to * }
    export_assignments
    # map -> fit -> sta, no assembler (no bitstream is wanted from a sweep)
    foreach tool {map fit} {
        if {[catch {execute_module -tool $tool} err]} {
            project_close
            error "quartus_$tool failed at $freq MHz: $err"
        }
    }
    if {[catch {execute_module -tool sta -args "--do_report_timing"} err]} {
        project_close
        error "quartus_sta failed at $freq MHz: $err"
    }
    project_close
    # per-FUB slack / delay / levels
    set sta_bin [file join [file dirname [info nameofexecutable]] quartus_sta]
    if {[catch {exec $sta_bin -t [file join $script_dir sta_reports.tcl] $TOP >& sta_reports.log} err]} {
        puts stderr "  WARNING: sta_reports.tcl failed at $freq MHz (see $point_dir/sta_reports.log): $err"
    }
}

# ---- sweep ----------------------------------------------------------------------
set failed {}
foreach freq $FREQS_MHZ {
    set period    [format %.4f [expr {1000.0 / $freq}]]
    set point_dir [file join $BUILD_DIR ${freq}MHz]
    set rpt_dir   [file join $REPORTS_DIR sweep_${freq}MHz]
    file mkdir $point_dir $rpt_dir
    set sdc [file join $point_dir timing_target.sdc]
    write_sdc_wrapper $sdc $freq $INPUT_DELAY_FRACTION $OUTPUT_DELAY_FRACTION $CLK_UNCERTAINTY_NS $MASTER_SDC
    puts ""
    puts "================================================================"
    puts " sweep point: $freq MHz  (period $period ns)  -> $point_dir"
    puts "================================================================"
    if {$dry_run} {
        puts "  would compile $TOP for $DEVICE with SDC $sdc"
        continue
    }
    set t0 [clock seconds]
    if {[catch {run_point $freq $point_dir $sdc} err]} {
        puts stderr "  FAILED: $err"
        lappend failed $freq
        continue
    }
    # archive what the aggregator and a reader need
    foreach f [list output_files/$TOP.sta.summary output_files/$TOP.fit.summary output_files/$TOP.map.summary \
                    output_files/$TOP.sta.rpt fub_slack.csv fmax_summary.txt setup_worst.txt timing_target.sdc] {
        set src [file join $point_dir $f]
        if {[file exists $src]} { file copy -force $src $rpt_dir }
    }
    puts "  done in [expr {[clock seconds] - $t0}] s; reports -> $rpt_dir"
}

puts ""
if {[llength $failed]} {
    puts stderr "sweep finished with failures at: $failed MHz"
    exit 1
}
if {$dry_run} {
    puts "dry run complete: [llength $FREQS_MHZ] SDC wrapper(s) written under $BUILD_DIR"
} else {
    puts "sweep complete. Aggregate with:"
    puts "  python3 $flow_root/tools/parse_timing_sweep.py --tool quartus $REPORTS_DIR $REPORTS_DIR/sweep_wns.csv"
}
