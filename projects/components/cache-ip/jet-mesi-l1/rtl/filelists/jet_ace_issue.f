# Filelist for jet_ace_issue
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_ace_issue.f
#
# Combinational cache-event -> ACE-transaction map per MAS ch03/03 Table
# (the onyx D2 coherent subset): ARSNOOP stamp on the fill engine's AR,
# AWSNOOP=WriteBack stamp on the drain engine's AW, the AW-only Evict
# generator with the AWONLY_ID BID-swallow on the B channel (present but
# unexercised on jet v1 -- no EVICT/MAKE_UNIQUE events).  Own RTL only;
# foreign sources via their own filelists.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared cache-ip package (amber_ace_req_t)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# The combinational map itself
$JET_ROOT/rtl/fub/jet_ace_issue.sv
