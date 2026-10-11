#!/usr/bin/env bash
# ==============================================================================
# regr_loop.sh -- the `regr` meta-level repetition engine (make/tests.mk)
# ==============================================================================
#
# Called by the generated run-*-regr / run-all-regr targets. NOT a user entry
# point: use `make run-<stem>-regr[-parallel]` (or bin/regr_nightly_sweep.sh
# for the scheduled whole-repo sweep).
#
# Environment (set by the Makefile):
#   AREA       - test area name, for messages
#   XDIST      - pytest-xdist flags (e.g. "-n 48") or empty
#   WAVES      - "WAVES=1" or empty (passed into the rep environment)
#   TEST_CMD   - the pytest invocation (e.g. "python3 -m pytest -v ...")
#   TEST_COUNT - repetitions; default 10 (make TEST_COUNT=3 ... overrides)
#   COVERAGE   - when "1", COVERAGE=1 is passed into the rep environment
#
# Positional arguments: the test files for this invocation.
#
# Each repetition runs the FULL grid under one fresh RDS_SEED_BASE (the
# repo-root conftest derives every test's seed from it, so one base replays
# the whole rep; SEED= would pin every test to the SAME seed, which is why
# the base varies per rep instead). Builds are cached in sim_build across
# reps, so repetitions cost simulation time only.
#
# A failing rep fails the script immediately and prints the exact replay
# command for that seed base.
# ==============================================================================
set -uo pipefail

files=("$@")
if [ "${#files[@]}" -eq 0 ]; then
    echo "!! regr_loop: no test files given" >&2
    exit 2
fi

cnt="${TEST_COUNT:-10}"
base="$(date +%s)"
ok=0

for i in $(seq "$cnt"); do
    repbase=$((base + i))
    echo "${AREA:-regr}: regr rep ${i}/${cnt}  REG_LEVEL=FULL  RDS_SEED_BASE=${repbase}"
    # shellcheck disable=SC2086
    if REG_LEVEL=FULL RDS_SEED_BASE="${repbase}" ${WAVES:+$WAVES }${COVERAGE:+COVERAGE=1 } \
        ${TEST_CMD} ${XDIST} "${files[@]}"; then
        ok=$((ok + 1))
    else
        echo "!! ${AREA:-regr}: regr rep ${i}/${cnt} FAILED -- replay:" \
             "REG_LEVEL=FULL RDS_SEED_BASE=${repbase} ${TEST_CMD} ${XDIST} ${files[*]}" >&2
        exit 1
    fi
done

echo "${AREA:-regr}: regr green (${ok}/${cnt} reps)"
