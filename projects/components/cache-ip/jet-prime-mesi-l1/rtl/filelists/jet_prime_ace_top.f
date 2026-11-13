# Filelist for jet_prime_ace_top
# Location: projects/components/cache-ip/jet-prime-mesi-l1/rtl/filelists/jet_prime_ace_top.f
#
# The jet onyx-rig top (Task 9), recomposed onto the cache-ip planes
# (Task 4): jet_prime_cpu_plane + jet_prime_coh_core + l1_ace_plane (the ACE snoop
# responder + the shared l1_ace_issue Table 2.8.1 map + the
# axi4ace_master_rd/wr_monlite transports, D3 measured paths with ACE
# snoop fields + auto-pulsed RACK/WACK), plus the D-7 monbus_arbiter and
# the boundary reset_sync.  No coh_req sideband to the top level (the
# fabric is not in this rig; the launch stream feeds l1_ace_issue
# on-chip).  Own RTL: the top itself; foreign sources only via their own
# filelists.

# CPU plane (frontend + D-6 request skid + J4 response sequencer)
-f $JET_PRIME_ROOT/rtl/filelists/plane/jet_prime_cpu_plane.f

# Coherence-core plane (jet control closure + arrays/repl/engines +
# observers + the integration glue)
-f $JET_PRIME_ROOT/rtl/filelists/plane/jet_prime_coh_core.f

# ACE fabric plane (l1_snoop_resp, l1_ace_issue,
# axi4ace_master_rd/wr_monlite, sn_want_o)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_ace_plane.f

# Boundary reset synchronizer + D-7 MonBus arbiter (complete closures)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# The ACE rig top itself
$JET_PRIME_ROOT/rtl/top/jet_prime_ace_top.sv
