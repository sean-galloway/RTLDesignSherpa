#!/bin/bash
# Monitor characterization sweep (amba TASK-034): every monitor variant, the
# plain master/slave it wraps (to subtract), and the aggregation blocks, each
# synthesized and routed out of context with tcl/monitor_synth.tcl -- the
# bridge fixture's recipe (projects/components/fabric-gen-ip/bridge/fpga) plus report_power.
# One Vivado per module, JOBS of them at a time, each in its own scratch cwd so
# the journals do not collide; reports land in reports/<top>__<part>/ and one
# row per run is appended to reports/summary.csv.
#
#   bin/monitor_synth_sweep.sh                       # default matrix, Kintex-7 at 6.667 ns
#   TARGETS="xc7a100tcsg324-1:10.0" bin/monitor_synth_sweep.sh axi4_master_rd_mon axi4_master_rd_monlite
#   JOBS=4 bin/monitor_synth_sweep.sh
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
default_modules="axi4_master_rd axi4_master_rd_cg axi4_master_rd_mon axi4_master_rd_mon_cg axi4_master_rd_monlite axi4_master_rd_monlite_cg \
axi4_master_wr axi4_master_wr_mon axi4_master_wr_monlite axi4_slave_rd axi4_slave_rd_mon axi4_slave_rd_monlite \
axi5_master_rd axi5_master_rd_mon axi5_master_rd_monlite \
axil4_master_rd axil4_master_rd_mon axil4_master_rd_monlite axil4_master_wr axil4_master_wr_mon axil4_master_wr_monlite axil5_master_rd_monlite \
apb4_monitor apb5_monitor axis4_master_monlite axis4_master_monlite_cg wb4_monitor \
monbus_axil4_axil4_group monbus_axi4_axi4_group monbus_arbiter"
modules=${*:-$default_modules}
# part:period -- 150 MHz on the Kintex-7 (Genesys 2) by default; 100 MHz on the Artix-7 (Nexys A7) on request
targets=${TARGETS:-"xc7k325tffg900-2:6.667"}
jobs=${JOBS:-6}
mkdir -p "$here/reports" "$here/build"
run_one() {
  local m=$1 part=$2 ns=$3
  local fl="$repo/rtl/amba/filelists/$m.f"
  if [ ! -f "$fl" ]; then echo "SKIP $m: no filelist $fl" >&2; return 0; fi
  local wd; wd=$(mktemp -d "${TMPDIR:-/tmp}/monsynth_${m}_XXXX")
  ( cd "$wd" && BRIDGE_TOP=$m BRIDGE_PART=$part BRIDGE_CLK_NS=$ns FPGA_FILELIST=$fl REPO_ROOT=$repo FPGA_PROJECT_ROOT=$here \
      vivado -mode batch -notrace -source "$here/tcl/monitor_synth.tcl" > "$here/reports/${m}__${part}.log" 2>&1 )
  local rc=$?
  rm -rf "$wd"
  if [ $rc -ne 0 ]; then echo "FAILED $m on $part: see reports/${m}__${part}.log" >&2
  else grep '^SUMMARY' "$here/reports/${m}__${part}.log" >&2; fi
}
n=0
for t in $targets; do
  part=${t%%:*}; ns=${t##*:}
  for m in $modules; do
    n=$((n+1)); echo "[$n] $m on $part at $ns ns" >&2
    run_one "$m" "$part" "$ns" &
    while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do sleep 5; done
  done
done
wait
echo "done: $here/reports/summary.csv" >&2
