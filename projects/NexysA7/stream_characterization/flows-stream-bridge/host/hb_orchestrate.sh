#!/usr/bin/env bash
# hb_orchestrate.sh — half-beat end-to-end: wait for build -> check timing ->
# program -> characterize 1ch/4ch (compression off vs on) -> measure.
#
# Progress breadcrumbs: each phase touches a file under progress/ and updates
# progress/STATUS with a one-line "where am I". Watch with:
#     watch -n2 'ls -t progress/ ; echo ; cat progress/STATUS'
set -u
FLOW="/mnt/data/github/RTLDesignSherpa/projects/NexysA7/stream_characterization/flows-stream-bridge"
cd "$FLOW"
PROG="$FLOW/progress"
PORT="${PORT:-/dev/ttyUSB2}"
rm -rf "$PROG"; mkdir -p "$PROG"

mark() { touch "$PROG/$1"; echo "$(date +%H:%M:%S)  $1  ${2:-}" | tee "$PROG/STATUS"; }

source /mnt/data/github/RTLDesignSherpa/env_python >/dev/null 2>&1
export REPO_ROOT=/mnt/data/github/RTLDesignSherpa

# Tiny CSR reader: prints "<trace_records> <overflow> <tier1a> <tier1b> <tier1c> <tier0>"
read_csrs() {
python3 - "$PORT" <<'PY'
import sys
sys.path.insert(0,'/mnt/data/github/RTLDesignSherpa/projects/components/converters/bin')
sys.path.insert(0,'/mnt/data/github/RTLDesignSherpa/projects/NexysA7/stream_characterization/flows-stream-bridge/host')
from uart_axi_bridge import UARTAxiBridge
H=0x10000
with UARTAxiBridge(port=sys.argv[1], baudrate=115200) as b:
    wr=b.read(H+0x08)&0xffffffff; ov=b.read(H+0x0c)&1
    a=b.read(H+0x1E0)&0xffffffff; bb=b.read(H+0x1E4)&0xffffffff
    c=b.read(H+0x1E8)&0xffffffff; t0=b.read(H+0x1EC)&0xffffffff
    print(wr, ov, a, bb, c, t0)
PY
}

# NOTE: run this only AFTER the bitstream build has finished. Do not poll for
# the build here -- `pgrep -f build_all.tcl` false-matches any shell whose text
# contains that string (incl. diagnostics), which hung an earlier run.

# ---- Phase 2: timing ------------------------------------------------------
if grep -q "All user specified timing constraints are met" reports/timing_summary.txt 2>/dev/null; then
    WNS=$(grep -m1 "Worst Slack" reports/timing_summary.txt | grep -oE "\-?[0-9]+\.[0-9]+ns" | head -1)
    mark 20-timing-MET "WNS=$WNS"
else
    WNS=$(grep -m1 "Worst Slack" reports/timing_summary.txt 2>/dev/null | grep -oE "\-?[0-9]+\.[0-9]+ns" | head -1)
    mark 20-timing-FAILED "WNS=$WNS -- stopping before program"
    exit 1
fi

# ---- Phase 3: program -----------------------------------------------------
mark 30-programming
make program >"$PROG/program.log" 2>&1 && mark 35-programmed || { mark 35-program-FAILED; exit 1; }

# ---- Phase 4: characterize each config, compression OFF then ON -----------
# cfg "name:channels:config_name:size"
for cfg in "1ch:1:4desc_1ch_1MB:1MB" "4ch:4:16desc_4ch_256KB:256KB"; do
    nm="${cfg%%:*}"; rest="${cfg#*:}"; ch="${rest%%:*}"; rest="${rest#*:}"
    conf="${rest%%:*}"; sz="${rest##*:}"

    mark "40-${nm}-off-run"
    python3 host/run_characterization.py --port "$PORT" --compression off \
        --mon-config debug-all --size "$sz" --channels "$ch" --configs "$conf" \
        >"$PROG/${nm}-off.log" 2>&1
    read read_off ov_off a b c t0 < <(read_csrs)
    echo "$read_off" > "$PROG/${nm}-off-words"
    mark "41-${nm}-off-done" "wr_ptr_words=$read_off ov=$ov_off"

    mark "42-${nm}-on-run"
    python3 host/run_characterization.py --port "$PORT" --compression on \
        --mon-config debug-all --size "$sz" --channels "$ch" --configs "$conf" \
        >"$PROG/${nm}-on.log" 2>&1
    read read_on ov_on a b c t0 < <(read_csrs)
    recs=$((a+b+c+t0))
    # beats: words/2 (two 32-bit words per 64-bit beat). raw_beats = records*3.
    on_beats=$((read_on/2)); off_beats=$((read_off/2))
    redux="n/a"
    if [ "$off_beats" -gt 0 ]; then
        redux=$(python3 -c "print(f'{(1-$on_beats/$off_beats)*100:.1f}%')")
    fi
    {
      echo "config=$conf size=$sz channels=$ch"
      echo "  OFF: wr_ptr_words=$read_off  beats=$off_beats  ov=$ov_off"
      echo "  ON : wr_ptr_words=$read_on  beats=$on_beats  ov=$ov_on"
      echo "  compressor stats ON: records=$recs (A=$a B=$b C=$c tier0=$t0)"
      echo "  reduction (on vs off beats) = $redux"
    } | tee "$PROG/RESULT-$nm"
    mark "43-${nm}-on-done" "reduction=$redux"
done

mark 90-DONE
cat "$PROG"/RESULT-* > "$PROG/SUMMARY" 2>/dev/null
echo "=== SUMMARY ==="; cat "$PROG/SUMMARY"
