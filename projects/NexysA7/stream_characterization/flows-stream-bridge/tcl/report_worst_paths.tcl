#==============================================================================
# report_worst_paths.tcl — dump the top-N worst paths in detail after synth
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

open_project "$project_root/vivado_project/stream_char.xpr"
open_run synth_1 -name synth_1

file mkdir "$project_root/reports"
report_timing -max_paths 5 -nworst 1 -setup \
    -input_pins \
    -file "$project_root/reports/timing_worst5.txt"

puts "Wrote: $project_root/reports/timing_worst5.txt"
