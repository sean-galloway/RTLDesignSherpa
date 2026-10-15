#==============================================================================
# mig_example_impl.tcl -- place and route fb_mig's example design (K3 de-risk)
#==============================================================================
# Before MIG goes into the harness, prove the controller alone closes on this
# part with the board-proven pinout at DDR3-800: MIG's own example design
# (controller + AXI traffic generator), implemented to a routed design.
# No bitstream -- the example's status pins have no board location.
#
# Needs fpga/ip/build from vendor_ip.tcl. Writes reports/mig_example/.
#==============================================================================
set script_dir [file dirname [file normalize [info script]]]
set area       [file normalize "$script_dir/../.."]
set out        "$area/reports/mig_example"
set ex_dir     "$area/fpga/ip/build/mig_example"
file mkdir $out

open_project "$area/fpga/ip/build/fb_vendor_ip.xpr"
file delete -force $ex_dir
open_example_project -force -dir $ex_dir [get_ips fb_mig]
# In batch mode open_example_project leaves the IP project current; running
# impl_1 there places the fabric legs' top, not MIG. Switch explicitly.
close_project
set ex_xpr [glob "$ex_dir/*/*.xpr"]
open_project $ex_xpr
puts "mig_example_impl: top [get_property top [current_fileset]] in $ex_xpr"
launch_runs impl_1 -jobs 8
wait_on_run impl_1
if {[get_property PROGRESS [get_runs impl_1]] != "100%"} {
    puts stderr "ERROR: fb_mig example implementation failed"
    exit 1
}
open_run impl_1
report_utilization      -file "$out/utilization.txt"
report_timing_summary   -file "$out/timing_summary.txt"
report_io               -file "$out/io.txt"
report_drc              -file "$out/drc.txt"
set wns [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -setup]]
set whs [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -hold]]
set fh [open "$out/summary.txt" w]
puts $fh "wns_ns $wns"
puts $fh "whs_ns $whs"
close $fh
puts "\nmig_example_impl: routed, WNS $wns ns, WHS $whs ns -> $out"
