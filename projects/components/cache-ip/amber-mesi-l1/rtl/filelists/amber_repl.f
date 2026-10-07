# Filelist for amber_repl
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_repl.f
#
# Replacement-policy engine. Flops with reset, so the reset macro header
# comes first, then the package, then the module.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

$AMBER_ROOT/rtl/fub/amber_repl.sv
