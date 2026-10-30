# Filelist for jet_top
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_top.f
#
# The jet pair-rig top (Task 8): the jet control closure (jet_control +
# jet_mshr + jet_wb_buffer + jet_rsp_seq) composed with the UNCHANGED
# common-ip slice (arrays, repl, frontend, fill/drain engines, snoop
# responder, monlite observer) and the house AXI4 transports the core
# deliberately does not contain (DECISION D3: axi4_master_rd/wr_monlite),
# plus the D-7 MonBus arbiter and the boundary reset synchronizer.
# Own RTL: the top itself; foreign sources only via their own filelists.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Packages (l1_pkg first; jet_pkg closes it)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f
-f $JET_ROOT/rtl/filelists/jet_pkg.f

# jet control closure (the lookup/commit core + its three files)
-f $JET_ROOT/rtl/filelists/jet_mshr.f
-f $JET_ROOT/rtl/filelists/jet_wb_buffer.f
-f $JET_ROOT/rtl/filelists/jet_rsp_seq.f
-f $JET_ROOT/rtl/filelists/jet_control.f

# Common-ip slice: arrays + replacement + GAXI frontend.  The engine
# filelists are -f'd whole (the audit's cross-area rule); their transport
# closures (axi4_master_rd/wr) overlap the monlite variants below, which
# the filelist resolution dedups -- jet_top instantiates only the
# monlite-wrapped transports (DECISION D3).
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_tag_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_data_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_repl.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_frontend.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_fill.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_drain.f

# ACE snoop responder + MonBus observer (their own closures)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_snoop_resp.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_monlite.f

# Jet J7 MonBus observer (glue in jet RTL; does NOT modify common-ip)
-f $JET_ROOT/rtl/filelists/jet_monlite.f

# Pair-rig bench memory slave (AXI4 SDP RAM, complete closure)
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f

# House AXI4 transports (D3), boundary reset sync, MonBus arbiter (D-7)
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_monlite.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_monlite.f
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# The pair-rig top itself
$JET_ROOT/rtl/top/jet_top.sv
