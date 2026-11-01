# Filelist for l1_ace_issue
# Location: projects/components/cache-ip/common-ip/rtl/filelists/fub/l1_ace_issue.f
#
# Combinational cache-event -> ACE-transaction map per MAS ch02/08 Table
# 2.8.1 (the onyx D2 coherent subset): ARSNOOP stamp on the fill engine's
# AR, AWSNOOP=WriteBack stamp on the drain engine's AW, the AW-only Evict
# generator with the AWONLY_ID BID-swallow on the B channel. Shared FUB
# merged from amber_ace_issue / jet_ace_issue (modulo names/comments the
# two are identical; jet's AW-only path is present but unexercised).
# Own RTL only; foreign sources via their own filelists.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared cache-ip package (amber_ace_req_t)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# The combinational map itself
$CACHE_COMMON_ROOT/rtl/fub/l1_ace_issue.sv
