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
        # Expand ANY $VAR from the environment, not just $REPO_ROOT. The
        # filelists this pulls in (converters, common) use $CONVERTERS_ROOT
        # and friends, and a reader that only knew $REPO_ROOT failed on the
        # first one with a literal "$CONVERTERS_ROOT/..." path (2026-09-10).
        while {[regexp {\$([A-Za-z_][A-Za-z0-9_]*)} $line -> vname]} {
            if {![info exists ::env($vname)]} {
                error "filelist $path references \$$vname but it is not set in the environment"
            }
            regsub -all "\\\$$vname" $line [file normalize $::env($vname)] line
        }
        if {[string match "+incdir+*" $line]} {
            lappend incs [string range $line 8 end]
        } elseif {[string match "-f *" $line]} {
            read_flist [string trim [string range $line 2 end]] incs srcs
        } elseif {[string match "*.vlt" $line]} {
            # Verilator lint-waiver file -- simulator-only, and Vivado tries to
            # parse it as Verilog and dies on the first `-` (2026-09-10).
            continue
        } else {
            lappend srcs $line
        }
    }
    close $fh
}

set incdirs {}
set srcs {}
read_flist "$self/rtl/filelists/litedram_char_board.f" incdirs srcs

foreach s $srcs {
    if {[string match "*.v" $s]} { read_verilog $s } else { read_verilog -sv $s }
}

read_xdc "$self/constraints/litedram_char.xdc"
# The generated core XDC carries NO pins (the harness XDC keeps the full Nexys
# A7 pin map) but it DOES carry LiteX's reset-synchroniser false paths
# (mr_ff / ars_ff1 / ars_ff2 cell attributes). Without it the core's 75 MHz
# reset strobe -> 100 MHz CRG reset-sync FDCE is timed as a real 3.3 ns
# cross-domain path and fails by ~2 ns (2026-09-10, WNS -1.966 on exactly that
# endpoint). Read it AFTER ours so it only adds the false paths.
read_xdc "$self/build_board/gateware/litedram_core.xdc"

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
