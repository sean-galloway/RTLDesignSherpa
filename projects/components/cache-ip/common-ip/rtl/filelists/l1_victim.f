# Filelist for l1_victim
# Location: projects/components/cache-ip/common-ip/rtl/filelists/l1_victim.f
#
# Depth-1 victim buffer (MAS ch02_blocks/05): one dirty line held while its
# write-back (drain) is outstanding. Instantiated by l1_control.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

$CACHE_COMMON_ROOT/rtl/fub/l1_victim.sv
