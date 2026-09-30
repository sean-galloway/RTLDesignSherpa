#!/usr/bin/env bash
# Behavioural probe for the ZQ arm of scoria_cmd_arbiter.
#
# This is NOT the DV suite -- scoria's dv/ is still empty and the cocotb suite
# is a separate build-out. It exists because "the ZQ branch lints clean" says
# nothing about whether the branch can be REACHED, and a check that cannot fail
# is not a check (the same lesson the ILA trigger-arming proof taught: a silent
# `contend` only means something once `dqonly` and `rdonly` are shown to fire).
#
# So CASE0 proves ordinary read traffic issues with ZQ idle. Only then does
# CASE1's "zero commands inside the tZQCS window" carry information.
#
#   CASE0  read work issues with ZQ idle          -> the pipeline is live
#   CASE1  ZQCS fires, grant aligns, then silence -> JESD79-3F 3.10 block holds
#   CASE2  two open banks are PRECHARGED first    -> all-idle precondition holds
#
# Usage: source env_python first, then run from anywhere.
set -euo pipefail
REPO=$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)
SC=$REPO/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3
OUT=${TMPDIR:-/tmp}/scoria_zq_probe
rm -rf "$OUT" && mkdir -p "$OUT"

# flatten first: verilator treats a nested -f as a SOURCE file, which once
# produced 7 bogus failures out of 9.
python3 "$REPO/bin/flatten_filelist.py" \
    "$SC/rtl/filelists/fub/scoria_cmd_arbiter.f" \
    --resolve-env --absolute-paths -o "$OUT/arb.f" >/dev/null

# PINMISSING is waived ON PURPOSE: the probe connects only the ports the ZQ arm
# depends on and leaves the other ~50 at their default, which is what makes a
# standalone TB for a 1500-line arbiter tractable at all.
verilator --binary -Wno-fatal -Wno-PINMISSING -Wno-WIDTH -Wno-UNUSED \
    -Wno-DECLFILENAME --timing \
    -I"$SC/rtl/includes" -f "$OUT/arb.f" "$SC/bin/zq_arm_probe.sv" \
    --top-module tb_zq --Mdir "$OUT/obj" -o simzq >"$OUT/build.log" 2>&1

"$OUT/obj/simzq" | tee "$OUT/run.log"
if grep -q FAIL "$OUT/run.log"; then echo "ZQ PROBE: FAILED"; exit 1; fi
grep -c PASS "$OUT/run.log" | xargs -I{} echo "ZQ PROBE: {} of 3 cases passed"
