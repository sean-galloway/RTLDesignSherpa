#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Out-of-repo proof for the bridge generator wheel (GitHub #119 L6).
#
# Builds the wheel from this checkout, installs it into a throwaway venv with
# no access to the repo's Python, then -- inside a foreign git repository, so
# the generator cannot mistake it for the IP root -- generates a fixture set,
# flattens each filelist with the packaged flattener, lints every top with
# Verilator, and byte-compares the emitted .sv with the committed bridges.
#
# Usage:  bin/package_check.sh [fixture ...]       (or: make package-check)
# Needs:  python3 with venv, network access for the wheel's PyPI dependencies,
#         verilator on PATH.

set -euo pipefail

BIN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BRIDGE_DIR="$(dirname "$BIN_DIR")"
COMMITTED="$BRIDGE_DIR/rtl/generated"
if [ "$#" -gt 0 ]; then
    FIXTURES=("$@")
else   # plain, mixed-protocol, cfg regblock (PeakRDL), master CDC, AXI5 + monitors
    FIXTURES=(bridge_2x2_rw bridge_mix_e bridge_1x2_rd_regblock bridge_2x2_rw_cdc bridge_1x2_rd_axi5)
fi

VERILATOR="$(command -v verilator || true)"
[ -n "$VERILATOR" ] || { echo "package-check: verilator not on PATH" >&2; exit 2; }

WORK="$(mktemp -d "${TMPDIR:-/tmp}/bridge-package-check.XXXXXX")"
trap 'rm -rf "${WORK:?}"' EXIT
echo "[package-check] work dir $WORK"

echo "[package-check] building the wheel"
python3 -m pip wheel "$BRIDGE_DIR" --no-deps --no-build-isolation -q -w "$WORK/dist"
rm -rf "${BRIDGE_DIR:?}/build" "$BIN_DIR"/*.egg-info
WHEEL="$(ls "$WORK"/dist/*.whl)"
echo "[package-check] $(basename "$WHEEL") ($(du -h "$WHEEL" | cut -f1))"

echo "[package-check] installing into a clean venv (PyPI dependencies)"
/usr/bin/env -i HOME="$HOME" PATH=/usr/bin:/bin python3 -m venv "$WORK/venv"
/usr/bin/env -i HOME="$HOME" PATH=/usr/bin:/bin "$WORK/venv/bin/pip" install -q "$WHEEL"

PROJ="$WORK/user_proj"
mkdir -p "$PROJ/cfg"
git -C "$PROJ" init -q
for c in "${FIXTURES[@]}"; do
    cp "$BIN_DIR/test_configs/$c.toml" "$BIN_DIR/test_configs/${c}_connectivity.csv" "$PROJ/cfg/"
done

# Everything below runs with the venv and verilator only: no repo PYTHONPATH.
CLEAN_PATH="$WORK/venv/bin:$(dirname "$VERILATOR"):/usr/bin:/bin"
REPO_TOP="$(cd "$BRIDGE_DIR/../../../.." && pwd)"
fail=0
run() { /usr/bin/env -i HOME="$HOME" PATH="$CLEAN_PATH" bash -c "cd '$PROJ' && $1"; }

for c in "${FIXTURES[@]}"; do
    if ! run "bridge-gen --ports cfg/$c.toml --output-dir rtl/generated > gen_$c.log 2>&1"; then
        echo "[package-check] FAIL generate $c (see $PROJ/gen_$c.log)"; fail=1
    fi
done

IP_ROOT="$(run 'bridge-gen --ip-root')"
case "$IP_ROOT" in "$REPO_TOP"/*) echo "[package-check] FAIL ip root is inside the checkout: $IP_ROOT"; fail=1 ;; esac

n_sv=0; n_diff=0
for d in "$PROJ"/rtl/generated/*/; do
    b="$(basename "$d")"
    if ! run "bridge-gen --flat-filelist rtl/filelists/$b.f > flat_$b.f 2> flat_$b.err"; then
        echo "[package-check] FAIL flatten $b: $(tail -1 "$PROJ/flat_$b.err")"; fail=1; continue
    fi
    if grep -q "^$REPO_TOP/\|+incdir+$REPO_TOP/" "$PROJ/flat_$b.f"; then
        echo "[package-check] FAIL $b flat list reaches into the checkout"; fail=1
    fi
    if run "verilator --lint-only -Wall -Wno-fatal -Wno-DECLFILENAME -Wno-UNUSEDSIGNAL -Wno-UNUSEDPARAM --top-module $b -f flat_$b.f > lint_$b.log 2>&1"; then
        errs=$(grep -c '^%Error' "$PROJ/lint_$b.log" || true)
        dups=$(grep -c 'MODDUP' "$PROJ/lint_$b.log" || true)
        echo "[package-check] lint $b: $(grep -vc '^+incdir' "$PROJ/flat_$b.f") files, $errs errors, $dups MODDUP"
        [ "$errs" = 0 ] && [ "$dups" = 0 ] || fail=1
    else
        echo "[package-check] FAIL lint $b (see $PROJ/lint_$b.log)"; fail=1
    fi
    for f in "$d"*.sv; do
        n_sv=$((n_sv + 1))
        cmp -s "$f" "$COMMITTED/$b/$(basename "$f")" || { n_diff=$((n_diff + 1)); echo "[package-check] differs from committed: $b/$(basename "$f")"; }
    done
done
echo "[package-check] $n_sv generated .sv compared with the committed bridges, $n_diff differ"
[ "$n_diff" = 0 ] || fail=1

if [ "$fail" = 0 ]; then echo "[package-check] PASS"; else echo "[package-check] FAIL"; trap - EXIT; echo "kept $WORK for inspection"; fi
exit "$fail"
