# Filelist for amber_snoop_resp
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_snoop_resp.f
#
# ACE snoop responder: wraps the house axi4ace_snoop_slave transport
# (cross-area sources are -f'd, never hand-listed -- filelist_registry
# --audit), adds the SR sequencing FSM and ACSNOOP translation.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/reset_defs.svh

-f $REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_pkg.f

-f $REPO_ROOT/rtl/amba/filelists/axi4ace_snoop_slave.f

$REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_snoop_resp.sv
