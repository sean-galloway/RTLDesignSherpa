#==============================================================================
# report_bram_hier.tcl — hierarchical BRAM breakdown after synth
#==============================================================================
# Opens the existing synth_1 run and emits a hierarchical utilization report
# so we can see which sub-blocks consume BRAM. Invoke after `make synth`.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

open_project "$project_root/vivado_project/stream_char.xpr"
open_run synth_1 -name synth_1

file mkdir "$project_root/reports"
report_utilization -hierarchical -hierarchical_depth 6 \
    -file "$project_root/reports/utilization_hier.txt"

puts "Hierarchical utilization report:"
puts "  $project_root/reports/utilization_hier.txt"
