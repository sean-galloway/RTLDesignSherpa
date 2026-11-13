# Filelist for jet_prime_control
# Location: projects/components/cache-ip/jet-prime-mesi-l1/rtl/filelists/jet_prime_control.f
#
# Lookup stage of the jet control core (Task 5): one-request-one-window
# classify (tag read + MSHR CAM + WB match + set claim count) with the
# four-class outcome HIT / MERGE / MISS_ALLOC / STALL.  jet_prime_control drives
# but does not instantiate the arrays/repl/MSHR/WB/rsp_seq blocks -- the
# integrator (jet_prime_top, or the DV harness) wires them.  Needs the reset
# macro header and jet_prime_pkg (which closes l1_pkg).

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_pkg.f

$JET_PRIME_ROOT/rtl/fub/jet_prime_control.sv
