# Equivalence unit for mc_cmd_arb_bank (memory-controllers MC-011): the DUT's own
# filelist, the golden copy's, and the lockstep harness. sby reads the two
# sv2v flats instead (see Makefile); this .f is the unit a linter parses.
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_cmd_arb_bank.f
-f $REPO_ROOT/formal/mc_common/mc_cmd_arb_bank/filelists/gold.f
$REPO_ROOT/formal/mc_common/mc_cmd_arb_bank/formal_cmd_arb_bank_equiv.sv
$REPO_ROOT/formal/mc_common/mc_cmd_arb_bank/formal_cmd_arb_bank_dual.sv
$REPO_ROOT/formal/mc_common/mc_cmd_arb_bank/formal_cmd_arb_bank_rdprio.sv
