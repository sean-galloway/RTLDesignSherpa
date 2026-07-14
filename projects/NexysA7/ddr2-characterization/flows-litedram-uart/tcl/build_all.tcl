# Non-project Vivado batch build for the LiteDRAM apples-to-apples char harness.
#   vivado -mode batch -source tcl/build_all.tcl   (REPO_ROOT must be exported)
set REPO_ROOT [file normalize $::env(REPO_ROOT)]
set self      [file normalize "[file dirname [info script]]/.."]
set part      xc7a100tcsg324-1

# ---- recursive filelist parser (+incdir / -f / source paths) ----
proc read_flist {path incs_var srcs_var} {
    upvar $incs_var incs
    upvar $srcs_var srcs
    global REPO_ROOT
    set fh [open $path r]
    foreach line [split [read $fh] "\n"] {
        set line [string trim $line]
        if {$line eq "" || [string index $line 0] eq "#"} continue
        regsub -all {\$REPO_ROOT} $line $REPO_ROOT line
        if {[string match "+incdir+*" $line]} {
            lappend incs [string range $line 8 end]
        } elseif {[string match "-f *" $line]} {
            read_flist [string trim [string range $line 2 end]] incs srcs
        } else {
            lappend srcs $line
        }
    }
    close $fh
}

set incdirs {}
set srcs {}
read_flist "$self/rtl/filelists/litedram_char_harness.f" incdirs srcs

foreach s $srcs {
    if {[string match "*.v" $s]} { read_verilog $s } else { read_verilog -sv $s }
}

read_xdc "$self/constraints/litedram_char.xdc"
# The LiteDRAM a7ddrphy IODELAY / ddram-pin constraints come from the generated
# core XDC. The shipped one has placeholder LOCs (X); a PROPER regen for the
# Nexys A7 target emits real pins. Read it once it is valid, and remove the
# ddram_* lines from litedram_char.xdc to avoid double-constraint.
# read_xdc "$self/build_board/gateware/litedram_core.xdc"

synth_design -top litedram_char_top -part $part -include_dirs $incdirs
opt_design
place_design
route_design
file mkdir "$self/bitstream"
file mkdir "$self/reports"
write_bitstream -force "$self/bitstream/litedram_char.bit"
report_timing_summary -file "$self/reports/timing.rpt"
report_utilization      -file "$self/reports/utilization.rpt"
puts "Bitstream: $self/bitstream/litedram_char.bit"
