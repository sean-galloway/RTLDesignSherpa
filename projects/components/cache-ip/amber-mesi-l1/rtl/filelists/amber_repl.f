# Filelist for amber_repl
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_repl.f
#
# Replacement-policy engine. Flops with reset, so the reset macro header
# comes first, then the package, then the module.

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

-f $REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_pkg.f

$REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_repl.sv
