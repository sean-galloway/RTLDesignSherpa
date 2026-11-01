# Filelist for jet_top
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_top.f
#
# The jet pair-rig top (Task 8), recomposed onto the cache-ip planes
# (Task 4): jet_cpu_plane (GAXI frontend + D-6 request skid + J4 response
# sequencer) + jet_coh_core (jet control closure + the UNCHANGED
# common-ip slice + the integration glue) + l1_axi4_plane (ACE snoop
# responder + the house AXI4 monlite transports, DECISION D3 + the
# AC-pending sn_want throttle), plus the D-7 monbus_arbiter and the
# boundary reset_sync.  Own RTL: the top itself; foreign sources only via
# their own filelists.

# CPU plane (frontend + D-6 request skid + J4 response sequencer)
-f $JET_ROOT/rtl/filelists/plane/jet_cpu_plane.f

# Coherence-core plane (jet control closure + arrays/repl/engines +
# observers + the integration glue)
-f $JET_ROOT/rtl/filelists/plane/jet_coh_core.f

# AXI4 fabric plane (l1_snoop_resp, axi4_master_rd/wr_monlite, D-8
# sideband pass-through, sn_want_o)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_axi4_plane.f

# Boundary reset synchronizer + D-7 MonBus arbiter (complete closures)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# Pair-rig bench memory slave (AXI4 SDP RAM, complete closure); carried
# here because jet_pair_rig_tb merges jet_top.f + jet_pair_fabric.f.
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f

# The pair-rig top itself
$JET_ROOT/rtl/top/jet_top.sv
