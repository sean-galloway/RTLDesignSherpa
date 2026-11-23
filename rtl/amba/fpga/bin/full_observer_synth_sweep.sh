#!/bin/bash
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
run_label=${RUN_LABEL:?"set RUN_LABEL to an isolated measurement name"}
jobs=${JOBS:-4}
rows=${*:-"feature_master feature_slave deploy_full deploy_lite"}
targets=${TARGETS:-"xc7k325tffg900-2:6.667 xc7a100tcsg324-1:10.0"}
results="$here/results/full_observer_$run_label"
mkdir -p "$results"
csv="$results/summary.csv"
echo "row,part,top,clk_ns,luts,ffs,lutram,bram_tiles,wns_reg2reg_ns,worst_logic_levels,unrouted_nets,seconds" > "$csv"

run_one() {
  local row=$1 part=$2 ns=$3
  local top fl generics
  case "$row" in
    feature_master|feature_slave)
      if [ "$row" = feature_master ]; then
        top=axi4_intf_master_observer_full
      else
        top=axi4_intf_slave_observer_full
      fi
      fl="$repo/projects/components/utility-ip/misc/rtl/filelists/${top}.f"
      generics="MAX_TRANSACTIONS=16 NUM_BANKS=1 N_ADDR_RANGES=4 TAP_ENABLE_ERROR_LOGIC=1 TAP_ENABLE_TIMEOUT_LOGIC=1 TAP_ENABLE_COMPL_LOGIC=1 TAP_ENABLE_THRESHOLD_LOGIC=1 TAP_ENABLE_PERF_LOGIC=1 TAP_ENABLE_DEBUG_LOGIC=1"
      ;;
    deploy_full|deploy_lite)
      if [ "$row" = deploy_full ]; then
        top=axi4_intf_master_observer_full
      else
        top=axi4_intf_master_observer
      fi
      fl="$repo/projects/components/utility-ip/misc/rtl/filelists/${top}.f"
      generics="MAX_TRANSACTIONS=64 NUM_BANKS=4"
      ;;
    *)
      echo "FAILED unknown row $row" >&2
      return 2
      ;;
  esac
  if [ ! -f "$fl" ]; then
    echo "FAILED $row: missing filelist $fl" >&2
    return 2
  fi

  local tag="${row}__${part}"
  local root="$results/$tag"
  local log="$results/$tag.log"
  mkdir -p "$root"
  local wd
  wd=$(mktemp -d "${TMPDIR:-/tmp}/full_observersynth_${row}_XXXX")
  ( cd "$wd" && BRIDGE_TOP="$top" BRIDGE_PART="$part" BRIDGE_CLK_NS="$ns" \
      FPGA_FILELIST="$fl" REPO_ROOT="$repo" FPGA_PROJECT_ROOT="$root" \
      SYNTH_GENERICS="$generics" HIER_DEPTH="${HIER_DEPTH:-8}" \
      vivado -mode batch -notrace -source "$here/tcl/monitor_synth.tcl" > "$log" 2>&1 )
  local rc=$?
  rm -rf "$wd"
  if [ $rc -ne 0 ]; then
    echo "FAILED $tag: see $log" >&2
    return $rc
  fi

  local summary="$root/reports/${top}__${part}/summary.txt"
  if [ ! -f "$summary" ]; then
    echo "FAILED $tag: no $summary" >&2
    return 1
  fi
  ( source "$summary"
    echo "$row,$part,$top,$clk_ns,$luts,$ffs,$lutram,$bram_tiles,$wns_reg2reg_ns,$worst_logic_levels,$unrouted_nets,$seconds" >> "$csv"
    echo "ROW $row part=$part LUT=$luts FF=$ffs LUTRAM=$lutram BRAM=$bram_tiles WNS_R2R=$wns_reg2reg_ns unrouted=$unrouted_nets" >&2
  )
}

pids=""
for target in $targets; do
  part=${target%%:*}
  ns=${target##*:}
  for row in $rows; do
    echo "RUN $row on $part at $ns ns" >&2
    run_one "$row" "$part" "$ns" &
    pids="$pids $!"
    while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do sleep 5; done
  done
done
rc=0
for pid in $pids; do
  wait "$pid" || rc=1
done
if [ $rc -ne 0 ]; then
  echo "FAILED: $csv" >&2
  exit 1
fi
echo "PASS: $csv" >&2
