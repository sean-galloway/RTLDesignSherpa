open_checkpoint [file join [pwd] reports_retry3a granite_char_top_retry3a_routed.dcp]
set fp [open [file join [pwd] reports_fp1/ramb_bounds.txt] w]
foreach st {RAMB36E1 RAMB18E1 DSP48E1} {
    set sites [get_sites -filter "SITE_TYPE == \"$st\""]
    if {[llength $sites] == 0} {
        puts $fp "$st: none"
        continue
    }
    set xs {}
    set ys {}
    foreach site $sites {
        set loc [get_property NAME $site]
        regexp {^([A-Za-z0-9_]+)_X([0-9]+)Y([0-9]+)$} $loc -> prefix x y
        lappend xs $x
        lappend ys $y
    }
    set xs [lsort -integer $xs]
    set ys [lsort -integer $ys]
    puts $fp "$st: [lindex $xs 0]..[lindex $xs end] X, [lindex $ys 0]..[lindex $ys end] Y"
}
close $fp
close_design
