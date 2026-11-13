# Filelist for jet_prime_mshr
# Location: projects/components/cache-ip/jet-prime-mesi-l1/rtl/filelists/jet_prime_mshr.f
#
# Miss address buffer (MAB): fully-associative CAM of outstanding misses
# (J1). Flops with reset, so the reset macro header comes first, then the
# package closure, then the module.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_pkg.f

$JET_PRIME_ROOT/rtl/fub/jet_prime_mshr.sv
