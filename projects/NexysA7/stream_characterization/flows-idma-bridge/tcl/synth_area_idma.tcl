# Parameterized OOC area synthesis for an iDMA component on xc7a100t.
# Env:
#   IDMA_TOP       top module
#   IDMA_FLISTS    space-separated .f files (deps + closure), order preserved
#   IDMA_INCDIRS   .f file listing include directories
#   IDMA_GENERICS  optional "Name=Val Name=Val" generics
#   IDMA_TAG       report tag -> reports/idma_area_<tag>.txt
set part_name "xc7a100tcsg324-1"
set here   [file normalize [file join [file dirname [info script]] ..]]
set top    $::env(IDMA_TOP)
set tag    $::env(IDMA_TAG)

create_project idma_area "$here/build/$tag" -part $part_name -force
set obj [current_project]
set_property target_language Verilog $obj
set src_fs [get_filesets sources_1]

# Sources from the listed .f files (comments / blanks skipped), order preserved.
set srcs {}
foreach flist [split $::env(IDMA_FLISTS)] {
    set fh [open $flist r]
    foreach line [split [read $fh] "\n"] {
        set line [string trim $line]
        if {$line eq "" || [string index $line 0] eq "#"} continue
        if {![file exists $line]} { puts "WARN missing: $line"; continue }
        lappend srcs $line
    }
    close $fh
}
add_files -norecurse -fileset $src_fs $srcs
foreach f [get_files -of_objects $src_fs] {
    if {[string match *.sv $f] || [string match *.svh $f]} {
        set_property FILE_TYPE SystemVerilog $f
    }
}

# Include dirs.
set incs {}
set fh [open $::env(IDMA_INCDIRS) r]
foreach line [split [read $fh] "\n"] {
    set line [string trim $line]
    if {$line ne "" && [file isdirectory $line]} { lappend incs $line }
}
close $fh
set_property include_dirs $incs $src_fs

if {[info exists ::env(IDMA_GENERICS)] && $::env(IDMA_GENERICS) ne ""} {
    set_property generic $::env(IDMA_GENERICS) $src_fs
}

set_property top $top $src_fs
update_compile_order -fileset sources_1
set_property -name {STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS} \
    -value {-mode out_of_context} -objects [get_runs synth_1]

reset_run synth_1
launch_runs synth_1 -jobs 4
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed for $top"
    exit 1
}
file mkdir "$here/reports"
open_run synth_1 -name synth_1
set rpt "$here/reports/idma_area_${tag}.txt"
report_utilization               -file $rpt
report_utilization -hierarchical -append -file $rpt
puts "IDMA AREA DONE ($top) -> $rpt"
