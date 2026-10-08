# Filelist for amber_victim
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_victim.f
#
# Depth-1 victim buffer (MAS ch02_blocks/05): one dirty line held while its
# write-back (drain) is outstanding. Instantiated by amber_control.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

$AMBER_ROOT/rtl/fub/amber_victim.sv
