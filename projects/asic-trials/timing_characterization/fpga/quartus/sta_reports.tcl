# ==============================================================================
# sta_reports.tcl -- per-FUB slack, data-path delay and logic levels
# ==============================================================================
# Run by syn_sweep_quartus.tcl after the fitter, inside the point directory:
#
#   quartus_sta -t sta_reports.tcl <project>
#
# Writes, beside the project:
#   fub_slack.csv      fub,slack_ns,data_delay_ns,logic_levels,from,to
#                      two rows per FUB: "<fub>" is the worst register-to-
#                      register setup path launched from that FUB's flops
#                      (the gate-delay signal the methodology wants), and
#                      "<fub>.io" is the worst path launched there to ANY
#                      endpoint, output ports included (the 20% output-delay
#                      budget lands on those). "design" is the worst path
#                      anywhere. The sweep aggregator reads this file.
#   fmax_summary.txt   report_clock_fmax_summary (restricted Fmax per clock)
#   setup_worst.txt    the worst setup path in full detail (for eyeballing)
#
# The FUB names match the generate-block labels in rtl/top/char_top.sv
# (gen_nand, gen_inv, ...); Quartus register names carry the hierarchy as
# `...gen_nand|...`, so `*gen_nand*` selects that FUB's flops.
# ==============================================================================

set proj [lindex $quartus(args) 0]
if {$proj eq ""} { set proj char_top }

project_open $proj -current_revision
create_timing_netlist -model slow
read_sdc
update_timing_netlist

report_clock_fmax_summary -file fmax_summary.txt
report_timing -setup -npaths 1 -detail full_path -file setup_worst.txt

set fubs {nand inv xor carry mult mux queue clkdiv gray}

# `paths` is a Timing Analyzer collection, not a Tcl list: `lindex` on it
# hands back the collection's internal id string, so walk it with
# foreach_in_collection and take the first (worst) path.
proc path_row {label paths} {
    if {[get_collection_size $paths] == 0} {
        return [list $label "" "" "" "" ""]
    }
    set p ""
    foreach_in_collection q $paths { set p $q; break }
    set slack  [get_path_info $p -slack]
    set delay  [get_path_info $p -data_delay]
    set levels [get_path_info $p -num_logic_levels]
    set from   [get_node_info [get_path_info $p -from] -name]
    set to     [get_node_info [get_path_info $p -to]   -name]
    return [list $label $slack $delay $levels $from $to]
}

set fh [open fub_slack.csv w]
puts $fh "fub,slack_ns,data_delay_ns,logic_levels,from,to"
# get_timing_paths, not get_path: get_path is delay-sorted and knows nothing
# of the clock constraint (every slack came back as minus the data delay,
# with 0 logic levels, on the first run). get_timing_paths -setup is the
# slack-sorted, constraint-aware collection report_timing itself uses, and
# get_path_info reads its objects.
set all_regs [get_registers *]
puts $fh [join [path_row design [get_timing_paths -setup -npaths 1]] ","]
foreach fub $fubs {
    set regs [get_registers -nowarn *gen_${fub}*]
    if {[get_collection_size $regs] == 0} {
        puts $fh "$fub,,,,,"
        puts $fh "$fub.io,,,,,"
        continue
    }
    puts $fh [join [path_row $fub      [get_timing_paths -setup -from $regs -to $all_regs -npaths 1]] ","]
    puts $fh [join [path_row "$fub.io" [get_timing_paths -setup -from $regs -npaths 1]] ","]
}
close $fh

delete_timing_netlist
project_close
