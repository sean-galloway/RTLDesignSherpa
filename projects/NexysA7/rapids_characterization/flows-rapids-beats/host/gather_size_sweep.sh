#!/usr/bin/env bash
# Clean transfer-size sweep on the Genesys 2 (8ch): the DUT wedges after a few
# back-to-back runs (snk_system_idle sticks), so we REPROGRAM before every size
# to guarantee a fresh state, run a single-config suite, and merge the per-size
# JSONs into one matrix the plot script consumes.
#
# Usage: source env_python; ./gather_size_sweep.sh <port> <out_matrix.json>
set -uo pipefail
PORT="${1:-/dev/ttyUSB1}"
OUT="${2:-projects/NexysA7/rapids_characterization/reports/perf/json/genesys_8ch_size_sweep.json}"
: "${REPO_ROOT:?source env_python first}"
FLOW="${REPO_ROOT}/projects/NexysA7/rapids_characterization/flows-rapids-beats"
export RAPIDS_CHAR_JTAG_SERIAL=200300B818A0
SIZES=(1 4 16 64 256 1024 4096)
TMPDIR="$(dirname "$OUT")/_size_parts"
mkdir -p "$TMPDIR"

for B in "${SIZES[@]}"; do
  echo "======== size ${B} beats: reprogram + single-config run ========"
  ( cd "$FLOW" && make program BOARD=genesys2 >/dev/null 2>&1 ) \
    && echo "  [programmed]" || { echo "  PROGRAM FAILED"; continue; }
  python3 "${FLOW}/host/run_characterization.py" \
    --port "$PORT" --channels 8 --suite --suite-channels 8 \
    --suite-beats "$B" --suite-bp off --suite-seeds default \
    --timeout 20 --results "${TMPDIR}/size_${B}.json" 2>&1 \
    | grep -iE 'SINK AXI4-wr|SOURCE AXIS-out|SINK:|SOURCE:' | grep -v 'Port-->'
done

echo "======== merge per-size parts -> ${OUT} ========"
python3 - "$OUT" "${TMPDIR}"/size_*.json <<'PY'
import json, sys
out = sys.argv[1]; parts = sys.argv[2:]
configs = []
for p in sorted(parts, key=lambda x: int(x.split('size_')[1].split('.')[0])):
    d = json.load(open(p))
    configs.extend(d.get('configs', []))
payload = {'total': len(configs),
           'passed': sum(1 for c in configs if c['pass']),
           'failed': sum(1 for c in configs if not c['pass']),
           'note': 'per-size fresh-programmed runs merged (DUT wedges across back-to-back runs)',
           'configs': configs}
json.dump(payload, open(out, 'w'), indent=2)
print(f"merged {len(configs)} configs -> {out} ({payload['passed']} passed)")
PY
