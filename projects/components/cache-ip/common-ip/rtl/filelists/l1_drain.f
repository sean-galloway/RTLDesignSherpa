# Filelist for l1_drain
# Location: projects/components/cache-ip/common-ip/rtl/filelists/l1_drain.f
#
# Drain path: AXI4 write-master sequencing engine (MAS ch02_blocks/06) driving
# the fub_axi_* upstream side of the house axi4_master_wr wrapper (DECISION
# D3). Victim beats forward directly from the latched payload register; the
# wrapper's AW/W/B skids absorb responder backpressure (DECISION D-6).

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# AXI4 write-master transport (complete closure; no rtl/amba sources hand-listed)
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr.f

$CACHE_COMMON_ROOT/rtl/fub/l1_drain.sv
