#!/bin/bash
# The reference set for HAS 6.4 / 5.3: the same bridges on both parts the
# repo's boards carry. Serial on purpose (the flow's build lock allows one
# Vivado per build directory). Usage: bin/synth_sweep.sh [bridge ...]
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
bridges=${*:-"bridge_2x2_rw bridge_2x2_rw_pipe bridge_2x2_rw_qos bridge_2x2_rw_cdc bridge_4x4_rw bridge_mix_a bridge_2x2_axi5 bridge_5x3_channels"}
# part:period -- 100 MHz on the Artix-7 (Nexys A7), 150 MHz on the Kintex-7 (Genesys 2)
targets="xc7a100tcsg324-1:10.0 xc7k325tffg900-2:6.667"
n=0; total=$(( $(echo $bridges | wc -w) * 2 ))
for b in $bridges; do
  for t in $targets; do
    part=${t%%:*}; ns=${t##*:}; n=$((n+1))
    echo "[$n/$total] $b on $part at $ns ns" >&2
    if ! make -C "$here" synth BRIDGE=$b PART=$part CLK_NS=$ns > "$here/reports/${b}__${part}.log" 2>&1; then
      echo "[$n/$total] FAILED: see reports/${b}__${part}.log" >&2
    else
      grep "^SUMMARY" "$here/reports/${b}__${part}.log" >&2
    fi
  done
done
echo "done: $here/reports/summary.csv" >&2
