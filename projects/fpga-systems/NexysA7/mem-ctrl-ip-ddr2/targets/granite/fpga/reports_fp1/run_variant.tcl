# run_variant.tcl -- Vivado floorplan variant place/route
# Usage: vivado -mode batch -source run_variant.tcl -tclargs <variant_number>
set v [lindex $argv 0]
if {$v eq ""} { set v 1 }

set run_dir [pwd]
set src [file join $run_dir build vivado_project ddr2_char.runs impl_1 granite_char_top_opt.dcp]
set outdir [file join $run_dir reports_fp1 v${v}]
file mkdir $outdir

set log [open [file join $outdir variant.log] w]
proc logmsg {msg} {
    upvar log log
    puts $log $msg
    flush $log
    puts $msg
    flush stdout
}

logmsg "Variant $v starting"
logmsg "Opening $src"
open_checkpoint $src

# Build floorplan per variant
switch $v {
    1 {
        # single pblock containing entry_store + sched_plane (union of current boxes)
        create_pblock pblock_store_sched
        resize_pblock pblock_store_sched -add {SLICE_X3Y0:SLICE_X89Y125 RAMB36_X2Y17:RAMB36_X3Y24}
        add_cells_to_pblock pblock_store_sched [get_cells -hier -filter {NAME =~ u_harness/u_dut/u_ctrl/u_core/u_entry_store*}]
        add_cells_to_pblock pblock_store_sched [get_cells -hier -filter {NAME =~ u_harness/u_dut/u_ctrl/u_core/u_sched_plane*}]
        logmsg "Created pblock_store_sched SLICE_X3Y0:SLICE_X89Y125 + RAMB36"
    }
    2 {
        # single pblock containing entry_store + sched_plane + axi_plane
        create_pblock pblock_all
        resize_pblock pblock_all -add {SLICE_X3Y0:SLICE_X89Y145 RAMB36_X2Y17:RAMB36_X3Y24}
        add_cells_to_pblock pblock_all [get_cells -hier -filter {NAME =~ u_harness/u_dut/u_ctrl/u_core/u_entry_store*}]
        add_cells_to_pblock pblock_all [get_cells -hier -filter {NAME =~ u_harness/u_dut/u_ctrl/u_core/u_sched_plane*}]
        add_cells_to_pblock pblock_all [get_cells -hier -filter {NAME =~ u_harness/u_dut/u_ctrl/u_core/u_axi_plane*}]
        logmsg "Created pblock_all SLICE_X3Y0:SLICE_X89Y145 + RAMB36"
    }
    3 {
        # two adjacent pblocks: store on left, sched on right (cmd_fifo+timers live in sched)
        create_pblock pblock_store
        resize_pblock pblock_store -add {SLICE_X3Y0:SLICE_X50Y125 RAMB36_X2Y17:RAMB36_X3Y24}
        add_cells_to_pblock pblock_store [get_cells -hier -filter {NAME =~ u_harness/u_dut/u_ctrl/u_core/u_entry_store*}]

        create_pblock pblock_sched
        resize_pblock pblock_sched -add {SLICE_X51Y0:SLICE_X79Y81}
        add_cells_to_pblock pblock_sched [get_cells -hier -filter {NAME =~ u_harness/u_dut/u_ctrl/u_core/u_sched_plane*}]
        logmsg "Created pblock_store SLICE_X3Y0:SLICE_X50Y125 + RAMB36 and pblock_sched SLICE_X51Y0:SLICE_X79Y81"
    }
    4 {
        # variant 1 sized ~20% larger (expand Y; X already full width)
        create_pblock pblock_store_sched
        resize_pblock pblock_store_sched -add {SLICE_X0Y0:SLICE_X89Y149 RAMB36_X2Y17:RAMB36_X3Y24}
        add_cells_to_pblock pblock_store_sched [get_cells -hier -filter {NAME =~ u_harness/u_dut/u_ctrl/u_core/u_entry_store*}]
        add_cells_to_pblock pblock_store_sched [get_cells -hier -filter {NAME =~ u_harness/u_dut/u_ctrl/u_core/u_sched_plane*}]
        logmsg "Created pblock_store_sched SLICE_X0Y0:SLICE_X89Y149 + RAMB36"
    }
    default {
        logmsg "Unknown variant $v"
        close $log
        exit 1
    }
}

# Placement
logmsg "Running place_design (default)..."
if {[catch {place_design} perr]} {
    logmsg "place_design default failed: $perr"
    logmsg "Retrying place_design -directive Explore..."
    if {[catch {place_design -directive Explore} perr2]} {
        logmsg "place_design Explore also failed: $perr2"
        report_timing_summary -file [file join $outdir timing_summary.txt] -max_paths 20
        write_checkpoint -force [file join $outdir granite_char_top_v${v}_place_failed.dcp]
        close $log
        close_design
        exit 1
    }
}
logmsg "place_design complete"

# Physical optimization
logmsg "Running phys_opt_design..."
if {[catch {phys_opt_design} perr]} {
    logmsg "phys_opt_design failed: $perr"
}

# Routing
logmsg "Running route_design..."
if {[catch {route_design} rerr]} {
    logmsg "route_design failed: $rerr"
    report_timing_summary -file [file join $outdir timing_summary.txt] -max_paths 20
    write_checkpoint -force [file join $outdir granite_char_top_v${v}_route_failed.dcp]
    close $log
    close_design
    exit 1
}
logmsg "route_design complete"

# Reports
logmsg "Generating reports..."
report_timing_summary -file [file join $outdir timing_summary.txt] -max_paths 20
report_timing -setup -max_paths 20 -file [file join $outdir timing_worst.txt]
write_checkpoint -force [file join $outdir granite_char_top_v${v}_routed.dcp]
logmsg "Variant $v finished"
close $log
close_design
