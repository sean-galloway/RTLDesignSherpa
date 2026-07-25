# Filelist for monbus_pkt_tally
# Location: rtl/amba/filelists/monbus_pkt_tally.f
#
# On-chip packet-type coverage histogram (SRAM count matrix + 32-entry LRU
# write-combining cache). Reuses monbus_cam as the cache front.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/monitor/monbus_cam.sv
$REPO_ROOT/rtl/amba/monitor/monbus_pkt_tally.sv
