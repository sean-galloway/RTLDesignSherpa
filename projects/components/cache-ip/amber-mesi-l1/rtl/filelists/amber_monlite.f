# Filelist for amber_monlite
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_monlite.f
#
# Drop-and-count MonBus observer (MAS ch04): emits 128-bit house-format
# packets for the Table 4.1.1 event classes, PROTOCOL_CORE + house
# UNIT/AGENT ids, never stalls the observed path; packets the monbus will
# not take are dropped and counted, re-emitted as Error/AMBER_EV_DROPPED
# once the output queue drains (STREAM monitor-lite idiom).

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# House monitor packet format (single source of truth for the 128-bit layout)
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

# Shared amber package (AMBER_EV_* event codes, geometry)
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

$AMBER_ROOT/rtl/fub/amber_monlite.sv
