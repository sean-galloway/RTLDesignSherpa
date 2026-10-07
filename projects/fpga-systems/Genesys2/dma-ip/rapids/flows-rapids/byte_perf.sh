#!/usr/bin/env bash
# One command: byte-RAPIDS characterization campaign -> results JSON -> report.
#   ./byte_perf.sh [--profile quick|standard|full] [--final] [--results FILE]
#                  [--port DEV] [--no-report] [--no-program] [--max-minutes N]
# Default is PRELIMINARY (results name carries _prelim). --final drops it; use
# that only after the bitstream carrying the channel-reset fix is programmed.
# If the board stops answering (another user reprogramming it) the campaign
# aborts without recording bogus failures; this script reprograms the
# bitstream and resumes, up to 3 times. Preflight (UART holder / other host
# scripts) runs before every program step and run; the results JSON carries the
# device readback (CSR_ID, BUILD, configure sentinel) at start and end of every
# session plus the bitstream sha256, and the run is invalid if they disagree.
set -u
SELF="$(cd "$(dirname "$0")" && pwd)"
RAPIDS="$(cd "$SELF/.." && pwd)"
REPO_ROOT="$(cd "$RAPIDS/../../../.." && pwd)"
PROFILE=standard; PRELIM=--prelim; PORT=/dev/ttyUSB0; REPORT=1; PROGRAM=1
RESULTS=""; EXTRA=()
while [ $# -gt 0 ]; do
  case "$1" in
    --profile) PROFILE="$2"; shift 2;;
    --final) PRELIM=""; shift;;
    --results) RESULTS="$2"; shift 2;;
    --port) PORT="$2"; shift 2;;
    --no-report) REPORT=0; shift;;
    --no-program) PROGRAM=0; shift;;
    --max-minutes) EXTRA+=(--max-minutes "$2"); shift 2;;
    *) echo "unknown arg $1" >&2; exit 2;;
  esac
done
cd "$REPO_ROOT" && . ./env_python

# The Genesys 2 is shared and the flow makefiles lock by build dir, not by
# board. Refuse to program or run while anyone else holds the UART or is
# running another area's host script / a programming Vivado. Re-checked right
# before every program step and every run attempt.
preflight() {
  local holders others
  holders="$(fuser "$PORT" 2>/dev/null | tr -s ' ' | sed 's/^ *//')"
  if [ -n "$holders" ]; then
    echo "byte-perf.sh: ABORT: $PORT is held by pid(s): $holders" >&2
    ps -o pid,args -p ${holders//[!0-9 ]/} >&2 2>/dev/null
    return 1
  fi
  others="$(ps -eo pid,args | grep -E 'run_characterization|[a-z_]+_char\.py|uart_axi_bridge|uart_link|litex_term|dump_status|run_sink_once|vivado.*(program|\.bit)' \
            | grep -v -E 'grep|byte_perf\.sh' || true)"
  if [ -n "$others" ]; then
    echo "byte-perf.sh: ABORT: another host script or programmer is running:" >&2
    echo "$others" >&2
    return 1
  fi
  return 0
}
if [ -z "$RESULTS" ]; then
  TAG=""; [ -n "$PRELIM" ] && TAG="_prelim"
  RESULTS="$RAPIDS/reports/perf/json/rapids_byte_perf${TAG}_$(date +%Y%m%d_%H%M%S).json"
fi
mkdir -p "$(dirname "$RESULTS")"
RC=1
for attempt in 1 2 3; do
  preflight || exit 3
  python3 "$SELF/host/run_characterization.py" --byte-perf --profile "$PROFILE" $PRELIM \
      --port "$PORT" --channels 8 --results "$RESULTS" --resume "${EXTRA[@]}"
  RC=$?
  if ! python3 -c "import json,sys; sys.exit(0 if json.load(open('$RESULTS')).get('aborted') else 1)" 2>/dev/null; then
    break
  fi
  [ "$PROGRAM" = 1 ] || break
  echo "byte-perf.sh: device lost (attempt $attempt); reprogramming and resuming"
  preflight || exit 3
  (cd "$SELF" && make program) || break
  sleep 5
done
if [ "$REPORT" = 1 ]; then
  python3 "$RAPIDS/reports/make_byte_perf_report.py" --results "$RESULTS" || RC=$?
fi
echo "byte-perf.sh: results $RESULTS (rc=$RC)"
exit $RC
