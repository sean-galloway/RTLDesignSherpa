# Filelist for amber_ace_top
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_top.f
#
# ACE rig top: the onyx-rig cache top on the house ACE masters --
# l1_core + amber_ace_issue (the Table 2.8.1 map) + the
# axi4ace_master_rd/wr_monlite transports (D3 measured paths, ACE snoop
# fields + auto-pulsed RACK/WACK) + the D-7 monbus_arbiter. No coh_req
# sideband to the top level (the fabric is not in this rig; the launch
# stream feeds ace_issue on-chip). Own RTL: the top itself; foreign
# sources only via their own filelists.

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# The core closure (CPU plane + coherence core plane aggregate)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_core.f

# ACE snoop responder (moved out of l1_core in Task 1; amber_ace_top
# closes it at the top until Task 3's fabric plane)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_snoop_resp.f

# The Table 2.8.1 event->transaction map (shared common-ip FUB, Task 2)
-f $CACHE_COMMON_ROOT/rtl/filelists/fub/l1_ace_issue.f

# ACE read/write master monitors (complete closures; the ACE variants of
# the pair rig's axi4_master_rd/wr_monlite, DECISION D3/D-8 observation)
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_rd_monlite.f
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_wr_monlite.f

# Boundary reset synchronizer (amber_ace_top input aresetn is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

# Monbus arbiter closure
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# The ACE rig top itself
$AMBER_ROOT/rtl/top/amber_ace_top.sv
