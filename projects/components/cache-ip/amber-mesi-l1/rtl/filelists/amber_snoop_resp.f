# Filelist for amber_snoop_resp
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_snoop_resp.f
#
# ACE snoop responder: wraps the house axi4ace_snoop_slave transport
# (cross-area sources are -f'd, never hand-listed -- filelist_registry
# --audit), adds the SR sequencing FSM and ACSNOOP translation.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

-f $REPO_ROOT/rtl/amba/filelists/axi4ace_snoop_slave.f

$AMBER_ROOT/rtl/fub/amber_snoop_resp.sv
