#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# board_lock.sh -- run a command holding one board's exclusive lock.
#
#   board_lock.sh --board genesys2 -- vivado -mode batch -source program.tcl
#
# WHY THIS EXISTS. make/fpga_flow.mk's build lock is keyed on the BUILD
# DIRECTORY, which is correct for what it guards: build-mon and build-perf own
# separate Vivado project trees and must be able to run at the same time. A
# physical board is not contended that way. It is contended by its JTAG chain
# and its UART, so two areas take two different build locks and both drive one
# board -- and `program` lives in make/fpga_board.mk, which has no lock at all.
#
# 2026-09-30, five minutes apart: a scoria LiteDRAM board proof held
# /dev/ttyUSB0 until 09:34:51, and a rapids 8-channel byte-perf run started on
# the same Genesys 2 at 09:40:04. No harm that time.
#
# The failure it would have produced is the point. A harness records the sha256
# of the bitstream IT programmed, not what is on the device. A third party
# reprogramming mid-run leaves a results file with no error, no timeout and no
# golden mismatch -- while measuring someone else's design. fpga_board.mk
# already makes this argument one step short, for the HOLD fallback: "silently
# programming a different bitstream than the one you just built is a worse
# failure than refusing: it is how a board result gets attributed to the wrong
# design." Concurrent reprogramming is that failure with a different cause.
#
# KEYED ON THE JTAG SERIAL, because two boards can sit on ONE chain and the
# serial is the only thing that tells them apart. The BOARD name is the fallback
# for a board the registry has no serial for -- the same tolerance
# fpga_flow.mk's FPGA_JTAG_SERIAL has.
#
# The lock is taken on fd 9 and then `exec`d into the payload: open file
# descriptors survive exec, and an flock lives on the open file description, so
# the payload itself holds the lock for its whole life and the kernel drops it
# when the payload dies -- kill included. There is no stale lock to clean up by
# hand, and no PID file needing the liveness check that has failed this repo
# before. Killing MAKE rather than the payload orphans the payload, which keeps
# the lock until it finishes; that is the same behaviour the build lock has with
# vivado, and `fuser -v` on the lock names whoever is really holding it.
#
# Handbook: [[fpga/cmn-infra/boards]]

set -uo pipefail

SELF_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BOARD_CLI="$SELF_DIR/fpga_board.py"
PYTHON="${PYTHON:-python3}"
LOCK_DIR="${RDS_BOARD_LOCK_DIR:-/tmp}"
EXIT_BUSY=98

BOARD=""
while [ $# -gt 0 ]; do
    case "$1" in
        --board) BOARD="${2:-}"; shift 2 ;;
        --)      shift; break ;;
        -h|--help)
            sed -n '5,10p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *)       break ;;
    esac
done

if [ -z "$BOARD" ]; then
    echo "board_lock.sh: --board <name> is required" >&2
    exit 2
fi
if [ $# -eq 0 ]; then
    echo "board_lock.sh: no command given" >&2
    exit 2
fi

# The registry's JTAG serial is the board's real identity. An empty answer is
# fine and expected for a board with no serial recorded; fall back to the name.
key=""
if [ -f "$BOARD_CLI" ]; then
    key="$("$PYTHON" "$BOARD_CLI" --board "$BOARD" serial 2>/dev/null || true)"
fi
[ -n "$key" ] || key="$BOARD"
# Anything that reaches a filename gets sanitised; a serial is alphanumeric, but
# a BOARD name arriving from the environment is not guaranteed to be.
key="$(printf '%s' "$key" | tr -c 'A-Za-z0-9._-' '_')"

lock="$LOCK_DIR/rds-board-$key.lock"

if ! exec 9>"$lock"; then
    echo "board_lock.sh: cannot create lock file $lock" >&2
    exit 1
fi

if ! flock -n 9; then
    echo ""
    echo "====================================================================="
    echo " THIS BOARD IS IN USE BY ANOTHER FLOW"
    echo "   board : $BOARD"
    echo "   key   : $key"
    echo "   lock  : $lock"
    echo ""
    echo " Driving a board someone else is using does not fail loudly -- it"
    echo " produces measurements from the wrong bitstream. A harness records the"
    echo " sha256 of what IT programmed, not what is on the device, so the"
    echo " results file looks entirely valid."
    echo ""
    echo " The lock is per BOARD, not per build directory: another board is fine,"
    echo " and so is a Vivado build that does not touch hardware."
    echo ""
    echo " Holding it:"
    fuser -v "$lock" 2>&1 | sed 's/^/   /' || true
    echo ""
    echo " On the UART:"
    fuser -v /dev/ttyUSB* 2>&1 | sed 's/^/   /' || true
    echo ""
    echo " Wait for it. If you believe the holder is dead, confirm it is gone"
    echo " before doing anything else -- this lock is released by the kernel, so"
    echo " a live holder means a live process:"
    echo "   fuser -v $lock"
    echo "====================================================================="
    echo ""
    exit "$EXIT_BUSY"
fi

# fd 9 survives this exec and the lock travels with it, so the payload holds the
# board for its entire life rather than only while this script runs.
exec "$@"
