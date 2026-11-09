# Equivalence unit for mc_bank_timer (memory-controllers MC-011): the DUT's own
# filelist, the golden copy's, and the lockstep harness. sby reads the two
# sv2v flats instead (see Makefile); this .f is the unit a linter parses.
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_timer.f
-f $REPO_ROOT/formal/mc_common/mc_bank_timer/filelists/gold.f
$REPO_ROOT/formal/mc_common/mc_bank_timer/formal_bank_timer_equiv.sv
