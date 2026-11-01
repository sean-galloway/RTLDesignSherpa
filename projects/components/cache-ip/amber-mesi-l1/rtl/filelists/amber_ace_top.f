# Filelist for amber_ace_top
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_top.f
#
# ACE rig top: the onyx-rig cache top on the house ACE masters -- the three
# cache-ip planes (CPU plane, coherence-core plane, ACE fabric plane) plus
# the D-7 monbus_arbiter and boundary reset_sync. The ACE fabric plane
# contains l1_ace_issue (Table 2.8.1 map), l1_snoop_resp, and the
# axi4ace_master_rd/wr_monlite transports. No coh_req sideband reaches the
# top level. Own RTL: the top itself; foreign sources only via their own
# filelists.

# CPU plane (l1_cpu_frontend)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_cpu_plane.f

# Coherence-core plane (l1_control, arrays, repl, fill/drain, monlite)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_coh_core.f

# ACE fabric plane (l1_snoop_resp, l1_ace_issue, axi4ace_master_rd/wr_monlite)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_ace_plane.f

# Boundary reset synchronizer (amber_ace_top input aresetn is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

# The ACE rig top itself
$AMBER_ROOT/rtl/top/amber_ace_top.sv
