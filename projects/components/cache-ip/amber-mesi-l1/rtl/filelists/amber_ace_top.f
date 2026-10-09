# Filelist for amber_ace_top
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_top.f
#
# ACE rig top: the onyx-rig cache top on the house ACE masters --
# amber_core + amber_ace_issue (the Table 2.8.1 map) + the
# axi4ace_master_rd/wr_monlite transports (D3 measured paths, ACE snoop
# fields + auto-pulsed RACK/WACK) + the D-7 monbus_arbiter. No coh_req
# sideband to the top level (the fabric is not in this rig; the launch
# stream feeds ace_issue on-chip). Own RTL: the top itself; foreign
# sources only via their own filelists.

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# The core closure (nine landed FUBs + their house deps)
-f $AMBER_ROOT/rtl/filelists/amber_core.f

# The Table 2.8.1 event->transaction map (own RTL; pkg-only closure)
-f $AMBER_ROOT/rtl/filelists/amber_ace_issue.f

# ACE read/write master monitors (complete closures; the ACE variants of
# the pair rig's axi4_master_rd/wr_monlite, DECISION D3/D-8 observation)
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_rd_monlite.f
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_wr_monlite.f

# Monbus arbiter closure
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# The ACE rig top itself
$AMBER_ROOT/rtl/top/amber_ace_top.sv
