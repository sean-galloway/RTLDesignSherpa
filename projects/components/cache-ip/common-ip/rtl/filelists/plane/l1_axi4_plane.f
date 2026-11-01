# Filelist for l1_axi4_plane
# Location: projects/components/cache-ip/common-ip/rtl/filelists/plane/l1_axi4_plane.f
#
# AXI4 fabric plane for the cache-ip shared MESI L1: l1_snoop_resp,
# axi4_master_rd/wr_monlite transports, the AC-pending sn_want_o throttle,
# and the D-8 coh_req_* sideband export.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# ACE snoop responder
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_snoop_resp.f

# House AXI4 transports (D3 measured paths)
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_monlite.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_monlite.f

# D-7 MonBus arbiter (merges rd/wr transport observers)
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# The AXI4 fabric plane
$CACHE_COMMON_ROOT/rtl/plane/l1_axi4_plane.sv
