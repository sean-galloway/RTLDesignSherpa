# exploration.tcl - open routed retry3a checkpoint and dump floorplan data
set run_dir [pwd]
set outdir  [file join $run_dir reports_fp1]
file mkdir $outdir

open_checkpoint [file join $run_dir reports_retry3a granite_char_top_retry3a_routed.dcp]

set fp [open [file join $outdir device_and_boxes.txt] w]

# device grid bounds from SLICE sites
set slice_sites [get_sites -filter {SITE_TYPE =~ "SLICE*"}]
set xs {}
set ys {}
foreach site $slice_sites {
    set loc [get_property NAME $site]
    regexp {SLICE_X([0-9]+)Y([0-9]+)} $loc -> x y
    lappend xs $x
    lappend ys $y
}
set xs [lsort -integer $xs]
set ys [lsort -integer $ys]
set xmin [lindex $xs 0]
set xmax [lindex $xs end]
set ymin [lindex $ys 0]
set ymax [lindex $ys end]
puts $fp "DEVICE SLICE GRID BOUNDS: X=${xmin}..${xmax} Y=${ymin}..${ymax}"
puts $fp ""

proc bbox {fp name} {
    set cells [get_cells -hier -filter "NAME =~ ${name}*"]
    set locs [get_property LOC $cells]
    set xs {}
    set ys {}
    foreach loc $locs {
        if {$loc == ""} { continue }
        regexp {SLICE_X([0-9]+)Y([0-9]+)} $loc -> x y
        lappend xs $x
        lappend ys $y
    }
    if {[llength $xs] == 0} {
        puts $fp "$name BBOX: NO LOCATIONS FOUND"
        return
    }
    set xs [lsort -integer $xs]
    set ys [lsort -integer $ys]
    set cxmin [lindex $xs 0]
    set cxmax [lindex $xs end]
    set cymin [lindex $ys 0]
    set cymax [lindex $ys end]
    puts $fp "$name BBOX: SLICE_X${cxmin}Y${cymin} -> SLICE_X${cxmax}Y${cymax}  (width [expr {$cxmax-$cxmin+1}], height [expr {$cymax-$cymin+1}], cells [llength $cells])"
}

bbox $fp u_harness/u_dut/u_ctrl/u_core/u_entry_store
bbox $fp u_harness/u_dut/u_ctrl/u_core/u_sched_plane
bbox $fp u_harness/u_dut/u_ctrl/u_core/u_axi_plane
bbox $fp u_harness/u_dut/u_ctrl

close $fp

report_timing -setup -max_paths 20 -file [file join $outdir timing_worst20_paths.txt]
report_timing_summary -file [file join $outdir timing_summary.txt] -max_paths 20

set fp2 [open [file join $outdir worst20_endpoints.txt] w]
puts $fp2 "Worst 20 setup path start/end sites:"
set paths [get_timing_paths -setup -max_paths 20]
set i 1
foreach p $paths {
    set sp [get_property STARTPOINT_PIN $p]
    set ep [get_property ENDPOINT_PIN $p]
    set ssite [get_property LOC [get_cells -of_objects $sp]]
    set esite [get_property LOC [get_cells -of_objects $ep]]
    set slack [get_property SLACK $p]
    puts $fp2 "[format %2d $i] slack=$slack  start $ssite  end $esite  ($sp -> $ep)"
    incr i
}
close $fp2

write_checkpoint -force [file join $outdir explore_closed.dcp]
close_design
