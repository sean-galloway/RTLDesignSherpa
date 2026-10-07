#==============================================================================
# capture_ila_bug009.tcl -- program the rapids_char ILA bitstream, arm the ILA
# on the GO pulse, drive ONE single-channel sink run at the burst length under
# test (rapids BUG-009: a burst equal to the SRAM depth wedges the sink)
# (8 channels, 4 beats, seed 0xA5A5A5A5, no backpressure) over UART, and dump the
# observation-window trace (arm / open / close, the sink-ingress meter buckets,
# s_axis handshakes) to CSV.
#
# Usage:
#   FPGA_JTAG_SERIAL=200300B818A0 vivado -mode batch -source tcl/capture_ila_bug009.tcl \
#       [-tclargs <out.csv> <beats> <seed> <trigger_pos> <axlen>]
# Defaults: reports/ila_bug009_trace.csv, 4 beats, 0xA5A5A5A5, trigger at sample 128.
# The UART is auto-probed by the host script (RAPIDS_CHAR_UART overrides).
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set repo_root    [file normalize "$project_root/../../../../.."]   ;# flows -> rapids_beats -> Genesys2 -> fpga-systems -> projects -> repo
set bit "$project_root/bitstream/rapids_char_ila.bit"
set ltx "$project_root/bitstream/rapids_char_ila.ltx"
set out   [expr {$argc >= 1 ? [lindex $argv 0] : "$project_root/reports/ila_bug009_trace.csv"}]
set beats [expr {$argc >= 2 ? [lindex $argv 1] : 4096}]
set axlen [expr {$argc >= 5 ? [lindex $argv 4] : 127}]   ;# BUG-009: burst length (AxLEN), 127 = one SRAM depth
set seed  [expr {$argc >= 3 ? [lindex $argv 2] : "0xA5A5A5A5"}]
set tpos  [expr {$argc >= 4 ? [lindex $argv 3] : 128}]

set serial ""
foreach v {FPGA_JTAG_SERIAL RAPIDS_CHAR_JTAG_SERIAL} {
    if {[info exists ::env($v)] && $::env($v) ne ""} { set serial $::env($v); break }
}
if {$serial eq ""} {
    puts stderr "ERROR: set FPGA_JTAG_SERIAL (see 'make board-info' for this board's serial)."
    exit 1
}
set uart [expr {[info exists ::env(RAPIDS_CHAR_UART)] ? $::env(RAPIDS_CHAR_UART) : "auto"}]

open_hw_manager
connect_hw_server -allow_non_jtag
# A serial names a CABLE; an FT2232 exposes two channels and the serial is a
# prefix of both. Take the longest match that actually has a device.
set matches [lsearch -all -inline -glob [get_hw_targets] "*$serial*"]
if {[llength $matches] == 0} {
    puts stderr "ERROR: no JTAG target matching '$serial' in: [get_hw_targets]"; exit 1
}
set matches [lsort -command {apply {{a b} {expr {[string length $b] - [string length $a]}}}} $matches]
set tgt ""
foreach cand $matches {
    if {[catch {current_hw_target $cand; open_hw_target}]} {
        catch {close_hw_target}; catch {disconnect_hw_server}; connect_hw_server -allow_non_jtag; continue
    }
    if {[llength [get_hw_devices]] > 0} { set tgt $cand; break }
    catch {close_hw_target}
}
if {$tgt eq ""} { puts stderr "ERROR: '$serial' matched targets, none with a device."; exit 1 }
current_hw_device [lindex [get_hw_devices] 0]
refresh_hw_device -update_hw_probes false [current_hw_device]
set_property PROGRAM.FILE $bit [current_hw_device]
set_property PROBES.FILE  $ltx [current_hw_device]
if {[info exists ::env(ILA_NO_PROGRAM)]} {
    # The board already holds this bitstream and carries state from earlier
    # host runs that the capture must NOT erase (BUG-009 is history-dependent).
    puts "ILA_NO_PROGRAM set: keeping the current configuration and its state"
} else {
    program_hw_devices [current_hw_device]
}
refresh_hw_device [current_hw_device]
set ila [get_hw_ilas -of_objects [current_hw_device]]
puts "probes: [get_hw_probes -of_objects $ila]"

# Trigger on the GO pulse (r_go rises once per run, the cycle the window arms).
set p_go [lindex [get_hw_probes -of_objects $ila -filter {NAME =~ *r_go*}] 0]
if {$p_go eq ""} { puts stderr "ERROR: no r_go probe in $ltx"; exit 1 }

# Optional 6th arg: a "poison" pre-run at another AxLEN, driven BEFORE the ILA
# is armed. BUG-009 reproduces as: one AxLEN 255 run, then every later run
# wedges until the board is reprogrammed -- so the trace of interest is the
# run AFTER the 256-beat one.
set hostlog "$project_root/reports/ila_bug009_host.log"
set venv_py "$repo_root/venv/bin/python3"
set host    "$project_root/host/run_characterization.py"
set pre_axlen [expr {$argc >= 6 ? [lindex $argv 5] : -1}]
set pre_beats [expr {$argc >= 7 ? [lindex $argv 6] : $beats}]   ;# a SHORT pre-run (4 beats) is the second poison
if {$pre_axlen >= 0} {
    puts "Poison pre-run: ONE sink run at AxLEN $pre_axlen, $pre_beats beats (not captured) ..."
    set st [catch {exec env -i HOME=$::env(HOME) PATH=$repo_root/venv/bin:/usr/local/bin:/usr/bin:/bin \
                     PYTHONPATH=$repo_root/bin:$repo_root REPO_ROOT=$repo_root \
                     $venv_py $host --port $uart --channels 8 --active 1 --beats $pre_beats --base-seed $seed \
                     --sink-only --xfer-axlen $pre_axlen --timeout 20 \
                     --results $project_root/reports/ila_bug009_prerun.json >& $project_root/reports/ila_bug009_prerun.log} msg]
    puts "pre-run rc=$st"
}

if {[info exists ::env(ILA_TRIG_WRPROD)]} {
    # Trigger late in the run instead: when the AXI4-wr meter has counted
    # this many beats (decimal). The window then straddles the last burst.
    set p_wr [lindex [get_hw_probes -of_objects $ila -filter {NAME =~ *obs_wr_prod*}] 0]
    if {$p_wr eq ""} { puts stderr "ERROR: no obs_wr_prod probe in $ltx"; exit 1 }
    set_property TRIGGER_COMPARE_VALUE "eq32'u$::env(ILA_TRIG_WRPROD)" $p_wr
    puts "trigger: obs_wr_prod == $::env(ILA_TRIG_WRPROD)"
} else {
    set_property TRIGGER_COMPARE_VALUE eq1'b1 $p_go
}
set_property CONTROL.TRIGGER_POSITION $tpos $ila
set_property CONTROL.TRIGGER_CONDITION AND $ila
run_hw_ila $ila
puts "ILA armed on $p_go (trigger position $tpos)"

puts "Driving ONE sink run: 8 ch, $beats beats, seed $seed, bp off, over UART $uart ..."
# Run the host with an explicit environment rather than sourcing env_python
# under Vivado's shell (that failed silently: the venv python, PYTHONPATH and
# REPO_ROOT are all it needs). Tcl-level redirection so the log always exists.
set st [catch {exec env -i HOME=$::env(HOME) PATH=$repo_root/venv/bin:/usr/local/bin:/usr/bin:/bin \
                 PYTHONPATH=$repo_root/bin:$repo_root REPO_ROOT=$repo_root \
                 $venv_py $host --port $uart --channels 8 --active 1 --beats $beats --base-seed $seed \
                 --sink-only --xfer-axlen $axlen --timeout 20 --results $project_root/reports/ila_bug009_run.json >& $hostlog} msg]
set fh [open $hostlog r]; set hostout [read $fh]; close $fh
puts "host run (rc=$st): $msg\n$hostout"
if {$st != 0} { puts "host run failed (rc=$st) -- expected for the BUG-009 wedge; reading the trace anyway" }

wait_on_hw_ila -timeout 30 $ila
upload_hw_ila_data $ila
write_hw_ila_data -csv_file -force $out [current_hw_ila_data]
puts "ILA trace written: $out"
close_hw_manager
