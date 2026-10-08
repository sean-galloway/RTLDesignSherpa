# Filelist for amber_fill
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_fill.f
#
# Fill path: AXI4 read-master sequencing engine (MAS ch02_blocks/06) driving
# the fub_axi_* upstream side of the house axi4_master_rd wrapper (DECISION
# D3). R beats stage in a gaxi_fifo_sync DEPTH=4 (DECISION D-6).

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# R-beat staging queue (DECISION D-6)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

# AXI4 read-master transport (complete closure; no rtl/amba sources hand-listed)
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd.f

$AMBER_ROOT/rtl/fub/amber_fill.sv
