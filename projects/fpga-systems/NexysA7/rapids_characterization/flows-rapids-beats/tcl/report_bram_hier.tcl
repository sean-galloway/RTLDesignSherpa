#==============================================================================
# report_bram_hier.tcl — hierarchical BRAM breakdown after synth
#==============================================================================
# Opens the existing synth_1 run and emits a hierarchical utilization report so
# we can see which sub-blocks consume BRAM. RAPIDS beats has several deep SRAMs
# (descriptor RAM per half, per-channel data buffers), so this is the key report
# for judging whether a wider NUM_CHANNELS will fit the 100T.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

open_project "$project_root/build/vivado_project/rapids_char.xpr"
open_run synth_1 -name synth_1

file mkdir "$project_root/reports"
report_utilization -hierarchical -hierarchical_depth 6 \
    -file "$project_root/reports/utilization_hier.txt"

puts "Hierarchical utilization report:"
puts "  $project_root/reports/utilization_hier.txt"
