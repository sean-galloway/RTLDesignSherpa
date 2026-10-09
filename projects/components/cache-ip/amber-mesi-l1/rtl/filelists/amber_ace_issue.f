# Filelist for amber_ace_issue
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_issue.f
#
# Combinational cache-event -> ACE-transaction map per MAS ch02/08 Table
# 2.8.1 (the onyx D2 coherent subset): ARSNOOP stamp on the fill engine's
# AR, AWSNOOP=WriteBack stamp on the drain engine's AW, AW-only
# CleanUnique/MakeUnique/Evict origination with the AWONLY_ID BID-swallow
# on the B channel. Own RTL only; foreign sources via their own filelists.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package (amber_ace_req_t)
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# The combinational map itself
$AMBER_ROOT/rtl/fub/amber_ace_issue.sv
