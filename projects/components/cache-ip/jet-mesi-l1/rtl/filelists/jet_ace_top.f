# Filelist for jet_ace_top
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_ace_top.f
#
# The jet onyx-rig top (Task 9): jet_top's composition on the house ACE
# masters -- the jet control closure + the UNCHANGED common-ip slice +
# jet_ace_issue (the Table 2.8.1 map) + the axi4ace_master_rd/wr_monlite
# transports (D3 measured paths, ACE snoop fields + auto-pulsed
# RACK/WACK) + the D-7 monbus_arbiter.  No coh_req sideband to the top
# level (the fabric is not in this rig; the launch stream feeds
# jet_ace_issue on-chip).  Own RTL: the top itself; foreign sources only
# via their own filelists.

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
# the filelist resolution dedups.
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_tag_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_data_array.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_repl.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_frontend.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_fill.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_drain.f

# ACE snoop responder + MonBus observer (their own closures)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_snoop_resp.f
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_monlite.f

# The Table 2.8.1 event->transaction map (own RTL; pkg-only closure)
-f $JET_ROOT/rtl/filelists/jet_ace_issue.f

# House ACE transports (D3), boundary reset sync, MonBus arbiter (D-7)
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_rd_monlite.f
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_wr_monlite.f
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# The ACE rig top itself
$JET_ROOT/rtl/top/jet_ace_top.sv
