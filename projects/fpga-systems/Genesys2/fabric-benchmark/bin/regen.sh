#!/bin/bash
# ==============================================================================
# regen.sh -- regenerate every generated file of the Genesys 2 fabric benchmark
# ==============================================================================
# One input, every leg: rtl/bridges/configs/bridge_fb_data.toml (+ connectivity)
#   1. bridge generator  -> rtl/bridges/generated/bridge_fb_data/  (Leg A fabric)
#                           rtl/bridges/filelists/bridge_fb_data.f
#   2. gen_fabric_legs   -> rtl/generated/fb_data_fabric_bridge/   (Leg A wrapper)
#                           rtl/generated/fb_data_fabric_xbar/     (Leg B1 wrapper)
# Both steps always run together: a TOML change that reached only one leg is a
# topology mismatch between the legs, which is the one thing the benchmark
# cannot tolerate. RTL only -- this script writes no DV.
# ==============================================================================
set -euo pipefail
AREA="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="${REPO_ROOT:-$(git -C "$AREA" rev-parse --show-toplevel)}"
CFG="$AREA/rtl/bridges/configs"

echo "[regen] bridge_fb_data (Leg A fabric)"
python3 "$REPO_ROOT/projects/components/fabric-gen-ip/bridge/bin/bridge_generator.py" \
    --ports "$CFG/bridge_fb_data.toml" \
    --connectivity "$CFG/bridge_fb_data_connectivity.csv" \
    --name bridge_fb_data \
    --output-dir "$AREA/rtl/bridges/generated" > /dev/null
echo "[regen] fb_data_fabric wrappers (every leg)"
python3 "$AREA/bin/gen_fabric_legs.py"
echo "[regen] done"
