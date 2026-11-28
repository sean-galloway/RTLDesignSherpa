# Filelist for jet_prime_fill
# Location: projects/components/cache-ip/jet-prime-mesi-l1/rtl/filelists/jet_prime_fill.f
#
# Multi-outstanding AXI4 read-master fill engine (jet-prime TASK-001 step
# 2): one read ID per MSHR entry (plus the no-data upgrade slot), R demuxed
# by ID, beats presented with the entry's claimed set/way.  Drives the
# fub_axi_* upstream side of the house axi4_master_rd wrapper (DECISION
# D3); R beats stage in a gaxi_skid_buffer DEPTH=4 (DECISION D-6; flop-headed, ISSUE-001).  Replaces
# the shared single-outstanding l1_fill in jet_prime_coh_core.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Packages (l1_pkg first; jet_prime_pkg closes it)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f
-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_pkg.f

# R-beat staging queue (DECISION D-6)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

$JET_PRIME_ROOT/rtl/fub/jet_prime_fill.sv
