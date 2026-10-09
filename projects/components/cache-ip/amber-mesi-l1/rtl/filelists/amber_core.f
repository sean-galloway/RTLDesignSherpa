# Filelist for amber_core
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_core.f
#
# First end-to-end cache top (MAS ch01 hierarchy): pure structural
# integration of the nine landed FUBs. The core's memory side is the raw
# fub_axi_* master pins the engines drive -- the house axi4_master_rd/wr
# transports are a rig-top concern (DECISION D3, amber_top wraps the core
# "with" them), so amber_fill.f / amber_drain.f are NOT -f'd here: those
# lists additionally close the unit-test transports. The engines' true
# deps (reset macros, shared package, gaxi_fifo_sync) are named directly.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros (control/frontend/
# fill/drain/snoop_resp/monlite all use them; one include, first).
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# Leaf arrays + replacement engine (package-only closures)
-f $AMBER_ROOT/rtl/filelists/amber_tag_array.f
-f $AMBER_ROOT/rtl/filelists/amber_data_array.f
-f $AMBER_ROOT/rtl/filelists/amber_repl.f

# Blocking-pipeline control FSM (carries the pending_fill_bypass and
# victim leaves)
-f $AMBER_ROOT/rtl/filelists/amber_control.f

# CPU-facing GAXI slave (carries the DECISION D-6 response staging FIFO)
-f $AMBER_ROOT/rtl/filelists/amber_frontend.f

# Fill / drain sequencing engines (same-area sources; their own filelists
# additionally close the axi4_master_rd/wr unit-test transports, which the
# core deliberately does not instantiate -- DECISION D3)
# R-beat staging queue (DECISION D-6)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

$AMBER_ROOT/rtl/fub/amber_fill.sv
$AMBER_ROOT/rtl/fub/amber_drain.sv

# ACE snoop responder (carries the axi4ace_snoop_slave transport closure)
-f $AMBER_ROOT/rtl/filelists/amber_snoop_resp.f

# Drop-and-count MonBus observer (carries the monitor_common_pkg include,
# the D11 gaxi_fifo_sync observer queue closure)
-f $AMBER_ROOT/rtl/filelists/amber_monlite.f

$AMBER_ROOT/rtl/top/amber_core.sv
