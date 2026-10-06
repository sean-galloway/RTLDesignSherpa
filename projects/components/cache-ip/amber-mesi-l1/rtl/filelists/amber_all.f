# Master filelist for the amber component
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_all.f
#
# The lint/sim closure for the amber MESI L1. First RTL slice (2026-10-06):
# the shared package plus the three leaf blocks -- the snoop kmap decode and
# the tag/data arrays. Control-path blocks (amber_control, fill/drain,
# replacement, victim, snoop responder, ACE issue) join as they land.

-f $REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_pkg.f

$REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_snoop_kmap.sv
$REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_tag_array.sv
$REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_data_array.sv
$REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_repl.sv
$REPO_ROOT/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_snoop_resp.sv
