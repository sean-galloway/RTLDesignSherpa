#!/bin/bash
# Reproduce the third-party toolchain for the iDMA area flow (all gitignored):
#   - bin/bender         Bender v0.32.0 (filelist resolver)
#   - external/iDMA      PULP iDMA pinned to IDMA_REV, deps via `bender update`
#   - python deps        mario (mako/pyyaml/hjson) + OpenTitan reggen
# Idempotent; safe to re-run.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
IDMA_REV=3c0cc3fbaa8f4b35f82cc028b795cb12c35f90d9   # pulp-platform/iDMA
BENDER_VER=0.32.0
PY="${IDMA_PYTHON:-/mnt/data/github/RTLDesignSherpa/venv/bin/python}"

mkdir -p "$HERE/bin" "$HERE/external"

if [ ! -x "$HERE/bin/bender" ]; then
  echo "[setup] fetching bender $BENDER_VER"
  url="https://github.com/pulp-platform/bender/releases/download/v$BENDER_VER/bender-x86_64-unknown-linux-gnu.tar.xz"
  curl -sL "$url" -o /tmp/bender.tar.xz
  tar xJf /tmp/bender.tar.xz -C /tmp
  cp /tmp/bender-x86_64-unknown-linux-gnu/bender "$HERE/bin/bender"
  chmod +x "$HERE/bin/bender"
fi
"$HERE/bin/bender" --version

if [ ! -d "$HERE/external/iDMA/.git" ]; then
  echo "[setup] cloning iDMA @ $IDMA_REV"
  git clone https://github.com/pulp-platform/iDMA "$HERE/external/iDMA"
  git -C "$HERE/external/iDMA" checkout -q "$IDMA_REV"
fi

echo "[setup] resolving iDMA dependencies (bender update)"
mkdir -p "$HERE/external/iDMA/target/rtl/include"
( cd "$HERE/external/iDMA" && "$HERE/bin/bender" update )

echo "[setup] python deps (mario + OpenTitan reggen)"
"$PY" -m pip install -q mako pyyaml hjson tabulate mistletoe premailer

echo "[setup] done."
