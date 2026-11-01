# Filelist for l1_ace_plane
# Location: projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_ace_plane.f
#
# ACE fabric plane for the cache-ip shared MESI L1: l1_snoop_resp,
# l1_ace_issue (the shared Table 2.8.1 map), axi4ace_master_rd/wr_monlite
# transports, the AC-pending sn_want_o throttle, and the on-chip D-8
# coh_req_* consumption.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# ACE snoop responder
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_snoop_resp.f

# Shared ACE issue block (event -> ACE transaction map)
-f $CACHE_COMMON_ROOT/rtl/filelists/fub/l1_ace_issue.f

# House ACE transports (D3 measured paths, snoop fields + RACK/WACK)
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_rd_monlite.f
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_wr_monlite.f

# D-7 MonBus arbiter (merges rd/wr transport observers)
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# The ACE fabric plane
$CACHE_COMMON_ROOT/rtl/plane/l1_ace_plane.sv
