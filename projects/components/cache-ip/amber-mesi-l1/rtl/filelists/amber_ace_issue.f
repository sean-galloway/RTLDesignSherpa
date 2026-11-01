# Filelist for amber_ace_issue
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_issue.f
#
# Combinational cache-event -> ACE-transaction map per MAS ch02/08 Table
# 2.8.1 (the onyx D2 coherent subset): ARSNOOP stamp on the fill engine's
# AR, AWSNOOP=WriteBack stamp on the drain engine's AW, AW-only
# CleanUnique/MakeUnique/Evict origination with the AWONLY_ID BID-swallow
# on the B channel.
#
# The implementation now lives in cache-ip/common-ip as the shared
# l1_ace_issue FUB; this filelist is a thin amber-area wrapper so the
# existing unit test (_merge_sources('amber_ace_issue')) keeps working.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared cache-ip package (amber_ace_req_t)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# Shared combinational map
-f $CACHE_COMMON_ROOT/rtl/filelists/fub/l1_ace_issue.f
