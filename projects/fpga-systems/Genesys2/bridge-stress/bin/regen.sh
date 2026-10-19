#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Regenerate every generated file of the bridge stress model from its sources:
# the DUT bridge(s) and the configuration bridge from rtl/bridges/configs, and
# the three regblocks from rtl/regs/*.rdl. Delete-all-then-regenerate (Rule #0):
# nothing generated survives a run.
set -euo pipefail
AREA="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="${REPO_ROOT:-$(git -C "$AREA" rev-parse --show-toplevel)}"
CFG="$AREA/rtl/bridges/configs"
GEN="$AREA/rtl/bridges/generated"

if [ -z "${BS_REGEN_LOCKED:-}" ]; then
    exec env BS_REGEN_LOCKED=1 flock "$AREA/rtl/.regen.lock" bash "$0" "$@"
fi

rm -rf "$GEN" "$AREA/rtl/bridges/filelists" "$AREA/rtl/regs/generated" "$AREA/rtl/generated"
mkdir -p "$GEN"

for toml in "$CFG"/bridge_*.toml; do
    name="$(basename "$toml" .toml)"
    echo "[regen] $name"
    python3 "$REPO_ROOT/projects/components/fabric-gen-ip/bridge/bin/bridge_generator.py" \
        --ports "$toml" \
        --connectivity "$CFG/${name}_connectivity.csv" \
        --name "$name" \
        --output-dir "$GEN" > /dev/null
done

for rdl in "$AREA"/rtl/regs/*.rdl; do
    echo "[regen] $(basename "$rdl" .rdl)"
    python3 "$REPO_ROOT/bin/peakrdl_generate.py" "$rdl" \
        -o "$AREA/rtl/regs/generated" --no-html > /dev/null
done
# One harness per device under test (every bridge but the configuration one)
for toml in "$CFG"/bridge_*.toml; do
    [ "$(basename "$toml")" = "bridge_bs_cfg.toml" ] && continue
    python3 "$AREA/bin/gen_bs_harness.py" "$toml"
done
echo "[regen] done"
