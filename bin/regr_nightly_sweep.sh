#!/usr/bin/env bash
# ==============================================================================
# regr_nightly_sweep.sh -- scheduled whole-repo `regr` sweep
# ==============================================================================
#
# WHAT IT DOES
#   Runs the `regr` test level (make/tests.mk: the FULL grid, TEST_COUNT
#   repetitions with fresh random seeds each -- default 10) across the repo's
#   test areas, one area at a time, during the machine's idle window. It is
#   designed to be boring: it never fights an agent for an area, it resumes
#   where it left off, and it leaves a written report either way.
#
# WHY
#   Random-seed-exposed bugs are the class that single-seed regressions miss
#   (several real bugs in this repo only surfaced under a new seed). The
#   machine is idle roughly 21:00 -> 16:00 the next day, so a slow, wide,
#   low-priority sweep costs nothing.
#
# SMART SKIPPING (the important part)
#   An area is SKIPPED (not failed) when it looks actively worked on:
#     - any file under the area's val/ or rtl/ trees modified within the
#       last SWEEP_SKIP_MIN minutes (default 45), or
#     - a pytest/verilator process whose cwd or command line touches the
#       area's val/ or rtl/ trees is running (an agent working in a projects/
#       area that merely *uses* this area's RTL is visible while its
#       verilator compiles are in flight -- the cmdline carries the paths), or
#     - .git/index.lock exists (a commit/rebase is in flight).
#   Skips are recorded in the report with the reason. A skipped area is
#   simply a candidate for the next run; the sweep does NOT treat it as a
#   failure and does NOT retry it the same night.
#
# RESUME
#   State lives in reports/regr/state.txt ("area last-done-epoch"). Areas
#   finished since the current idle window opened (default 21:00) are not
#   re-run tonight; an interrupted sweep continues tomorrow. Delete the state
#   file to force a full sweep.
#
# OUTPUT (all under reports/regr/, which is gitignored)
#   reports/regr/<YYYY-MM-DD>/<area>.log   per-area make output
#   reports/regr/<YYYY-MM-DD>/REPORT.md    per-area status + failure details
#   reports/regr/state.txt                 resume state
#   reports/regr/cron.log                  cron stdout/stderr (when cron-driven)
#
# LOCAL LLM (optional)
#   If an Ollama server answers on OLLAMA_HOST (default http://localhost:11434),
#   the report gets an extra plain-language digest of the night's failures
#   (model = whatever /api/tags lists first). Purely best-effort: any failure
#   in the call is logged and ignored. The sweep never depends on it.
#
# USAGE
#   bin/regr_nightly_sweep.sh [--force] [--dry-run] [--areas "math cdc ..."]
#                             [--test-count N] [--skip-min N]
#   Environment overrides every knob (see CONFIG below). Without --force the
#   script refuses to run outside the idle window.
#
# ENABLE / DISABLE THE SCHEDULE (crontab on the host)
#   Enable : crontab -l 2>/dev/null | grep -v regr_nightly_sweep > /tmp/cron.$$
#            echo '7 21 * * * /mnt/data/github/RTLDesignSherpa/bin/regr_nightly_sweep.sh >> /mnt/data/github/RTLDesignSherpa/reports/regr/cron.log 2>&1' >> /tmp/cron.$$
#            crontab /tmp/cron.$$ && rm -f /tmp/cron.$$
#   Disable: crontab -l | grep -v regr_nightly_sweep | crontab -
#   (The install is one line; keep the script path absolute. `crontab -l` to
#   verify. The 21:07 start avoids the :00 herd and lands inside the window.)
#
# EXIT STATUS
#   0 -- all attempted areas green (skips do not affect the status)
#   1 -- at least one area went red (REPORT.md carries the replay commands)
# ==============================================================================
set -uo pipefail

# ------------------------------------------------------------------------------
# CONFIG (env overrides; defaults suit the amdtrp nightly idle window)
# ------------------------------------------------------------------------------
REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
AREAS="${AREAS:-common cdc math amba}"   # val/<area> dirs, small/fast first
AREA_RTL_common="rtl/common"             # rtl tree each area maps to (for the
AREA_RTL_cdc="rtl/cdc"                   # activity check); extend the map when
AREA_RTL_math="rtl/math"                 # adding an area, or export AREA_RTL_x
AREA_RTL_amba="rtl/amba"
TEST_COUNT="${TEST_COUNT:-10}"           # repetitions per area (regr level)
SWEEP_SKIP_MIN="${SWEEP_SKIP_MIN:-45}"   # recency window for "agent is working"
WINDOW_OPEN_HOUR="${WINDOW_OPEN_HOUR:-21}"   # idle window opens 21:00 ...
WINDOW_CLOSE_HOUR="${WINDOW_CLOSE_HOUR:-15}" # ... stop launching areas after 15:00
STATE_FILE="${STATE_FILE:-$REPO_ROOT/reports/regr/state.txt}"
OLLAMA_HOST="${OLLAMA_HOST:-http://localhost:11434}"
FORCE=0; DRY_RUN=0

while [ $# -gt 0 ]; do
    case "$1" in
        --force)      FORCE=1; shift ;;
        --dry-run)    DRY_RUN=1; shift ;;
        --areas)      AREAS="$2"; shift 2 ;;
        --test-count) TEST_COUNT="$2"; shift 2 ;;
        --skip-min)   SWEEP_SKIP_MIN="$2"; shift 2 ;;
        -h|--help)    sed -n '2,40p' "$0"; exit 0 ;;
        *) echo "!! unknown argument: $1 (see --help)" >&2; exit 2 ;;
    esac
done

# ------------------------------------------------------------------------------
# Housekeeping
# ------------------------------------------------------------------------------
cd "$REPO_ROOT" || { echo "!! cannot cd to $REPO_ROOT" >&2; exit 2; }
mkdir -p "$REPO_ROOT/reports/regr"
DAY="$(date +%F)"
OUT_DIR="$REPO_ROOT/reports/regr/$DAY"
mkdir -p "$OUT_DIR"
touch "$STATE_FILE"

log()  { printf '%s %s\n' "$(date '+%H:%M:%S')" "$*"; }
fail() { printf '%s %s\n' "$(date '+%H:%M:%S')" "$*" >&2; }

# ------------------------------------------------------------------------------
# Idle-window guard: the sweep is designed to run unattended overnight.
# ------------------------------------------------------------------------------
hour_now="$(date +%H | sed 's/^0//')"
in_window=0
if [ "$hour_now" -ge "$WINDOW_OPEN_HOUR" ] || [ "$hour_now" -lt "$WINDOW_CLOSE_HOUR" ]; then
    in_window=1
fi
if [ "$FORCE" -eq 0 ] && [ "$in_window" -eq 0 ]; then
    fail "refusing to run at $(date +%H:%M): outside the idle window" \
         "(${WINDOW_OPEN_HOUR}:00-${WINDOW_CLOSE_HOUR}:00). Use --force to override."
    exit 2
fi

# The window opened most recently (today 21:00, or yesterday 21:00 if before close).
if [ "$hour_now" -ge "$WINDOW_OPEN_HOUR" ]; then
    window_open_epoch="$(date -d "today ${WINDOW_OPEN_HOUR}:00" +%s)"
else
    window_open_epoch="$(date -d "yesterday ${WINDOW_OPEN_HOUR}:00" +%s)"
fi

# ------------------------------------------------------------------------------
# Activity probes
# ------------------------------------------------------------------------------
area_rtl() { eval "echo \"\${AREA_RTL_$1:-rtl/$1}\""; }

area_recently_touched() {  # $1 = area
    local rtl; rtl="$(area_rtl "$1")"
    find "val/$1" "$rtl" -type f -newermt "-${SWEEP_SKIP_MIN} minutes" \
        2>/dev/null | grep -q .
}

area_sim_running() {  # $1 = area: a sim whose cwd or command line touches
    local pid cwd cmd rtl # this area's val/ or rtl/ trees is "working there".
    rtl="$(area_rtl "$1")"
    for pid in $(pgrep -f 'pytest|verilator|vlt_wrapper' 2>/dev/null); do
        cwd="$(readlink "/proc/$pid/cwd" 2>/dev/null)" || continue
        case "$cwd" in
            "$REPO_ROOT/val/$1"|"$REPO_ROOT/val/$1"/*) return 0 ;;
        esac
        cmd="$(tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null)"
        case "$cmd" in
            *"/val/$1/"*|*"/$rtl/"*) return 0 ;;
        esac
    done
    return 1
}

git_locked() { [ -f "$REPO_ROOT/.git/index.lock" ]; }

area_done_this_window() {  # $1 = area
    local done_epoch
    done_epoch="$(awk -v a="$1" '$1==a {print $2}' "$STATE_FILE" 2>/dev/null | tail -1)"
    [ -n "$done_epoch" ] && [ "$done_epoch" -ge "$window_open_epoch" ]
}

mark_done() {  # $1 = area
    grep -v "^$1 " "$STATE_FILE" > "$STATE_FILE.tmp" 2>/dev/null || true
    echo "$1 $(date +%s)" >> "$STATE_FILE.tmp"
    mv "$STATE_FILE.tmp" "$STATE_FILE"
}

# ------------------------------------------------------------------------------
# Sweep
# ------------------------------------------------------------------------------
declare -a RESULTS=()   # "area:green|red|skip:<note>"
any_red=0

for area in $AREAS; do
    # Window: do not START a new area once the idle window is nearly over.
    hour_now="$(date +%H | sed 's/^0//')"
    if [ "$FORCE" -eq 0 ] && [ "$hour_now" -ge "$WINDOW_CLOSE_HOUR" ] && [ "$hour_now" -lt "$WINDOW_OPEN_HOUR" ]; then
        log "window closing (${WINDOW_CLOSE_HOUR}:00): stopping before '$area'"
        RESULTS+=("none:skip:window closed before launch")
        break
    fi

    if [ ! -d "val/$area" ]; then
        RESULTS+=("$area:skip:no val/$area directory")
        continue
    fi
    if area_done_this_window "$area"; then
        RESULTS+=("$area:skip:already green this window (resume state)")
        continue
    fi
    if git_locked; then
        RESULTS+=("$area:skip:.git/index.lock held (commit/rebase in flight)")
        continue
    fi
    if area_sim_running "$area"; then
        RESULTS+=("$area:skip:a simulation touching this area is running")
        continue
    fi
    if area_recently_touched "$area"; then
        RESULTS+=("$area:skip:files modified in the last ${SWEEP_SKIP_MIN}m (agent active)")
        continue
    fi

    log "sweeping $area (regr x${TEST_COUNT})"
    if [ "$DRY_RUN" -eq 1 ]; then
        RESULTS+=("$area:skip:dry-run")
        continue
    fi

    if ( cd "val/$area" && nice -n 10 env TEST_COUNT="$TEST_COUNT" \
            make run-all-regr-parallel ) > "$OUT_DIR/$area.log" 2>&1; then
        RESULTS+=("$area:green:")
        mark_done "$area"
        log "$area green"
    else
        any_red=1
        RESULTS+=("$area:red:see $OUT_DIR/$area.log (replay commands at the end)")
        log "!! $area RED -- see $OUT_DIR/$area.log"
    fi
done

# ------------------------------------------------------------------------------
# Report
# ------------------------------------------------------------------------------
REPORT="$OUT_DIR/REPORT.md"
{
    echo "# Nightly regr sweep -- ${DAY}"
    echo
    echo "Window: ${WINDOW_OPEN_HOUR}:00 -> ${WINDOW_CLOSE_HOUR}:00 (host $(hostname))."
    echo "Reps per area: ${TEST_COUNT}. Skips are not failures."
    echo
    echo "| Area | Status | Note |"
    echo "|---|---|---|"
    for r in "${RESULTS[@]}"; do
        IFS=':' read -r a st note <<< "$r"
        echo "| $a | $st | $note |"
    done
    echo
    for r in "${RESULTS[@]}"; do
        case "$r" in
            *:red:*)
                a="${r%%:*}"
                echo "## Failure details: $a"
                echo '```'
                grep -E "FAILED|AssertionError|REGR-FAIL|regr rep .* FAILED" \
                    "$OUT_DIR/$a.log" 2>/dev/null | sort -u | head -20
                echo '```'
                echo
                ;;
        esac
    done
} > "$REPORT"

# ------------------------------------------------------------------------------
# Optional local-LLM digest (best effort; never load-bearing)
# ------------------------------------------------------------------------------
if curl -s --max-time 3 "$OLLAMA_HOST/api/tags" > /dev/null 2>&1; then
    model="$(curl -s --max-time 3 "$OLLAMA_HOST/api/tags" \
             | grep -o '"name":"[^"]*"' | head -1 | cut -d'"' -f4)"
    if [ -n "$model" ]; then
        summary_text="$(for r in "${RESULTS[@]}"; do echo "$r"; done)"
        digest_prompt="You are summarizing an RTL regression sweep. Status lines (area:status:note), then failure excerpts. Write 5-8 plain sentences: what ran, what failed, and the single most likely next action. Be concrete.\n\n$summary_text"
        red_areas="$(for r in "${RESULTS[@]}"; do case "$r" in *:red:*) echo "${r%%:*}";; esac; done)"
        for a in $red_areas; do
            digest_prompt="$digest_prompt\n\n--- $a failures ---\n$(tail -40 "$OUT_DIR/$a.log" 2>/dev/null)"
        done
        digest="$(curl -s --max-time 120 -X POST "$OLLAMA_HOST/api/generate" \
            -H 'Content-Type: application/json' \
            -d "$(printf '{"model":"%s","prompt":"%s","stream":false}' "$model" \
                  "$(printf '%s' "$digest_prompt" | sed 's/\\/\\\\/g; s/"/\\"/g')")" \
            | grep -o '"response":"[^"]*"' | head -1 | cut -d'"' -f4)"
        if [ -n "$digest" ]; then
            { echo "## LLM digest (local model: $model)"; echo; echo "$digest"; echo; } >> "$REPORT"
        fi
    fi
fi

log "report: $REPORT"
exit "$any_red"
