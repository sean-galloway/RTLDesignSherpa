#!/usr/bin/env bash
# Fetch, pin, overlay and build Ramulator 2 for the mem-ctrl-ip models (MC-012).
#
# The clone lands in vendor/ramulator2 (gitignored, like every third-party
# source here). Upstream has no DDR2, so this repo carries an overlay: the
# DDR2 / DDR2_BL8 device classes, a timestamped trace frontend, their tests,
# and a 4-file registration patch for the upstream CMake source lists and the
# smoke-test table. Re-running is safe: the clone is reset to the pin, the
# overlay re-applied, the build incremental.
#
#   projects/components/mem-ctrl-ip/references/ramulator2/fetch.sh            # fetch + build
#   projects/components/mem-ctrl-ip/references/ramulator2/fetch.sh --test     # ... and run the suites
#
# Needs: git, cmake >= 3.20, a C++20 compiler (g++ 13 is what this was built
# with), python3 with dev headers (nanobind), and the repo venv (env_python)
# for pytest. The build target "codegen" rewrites src/ramulator/dram/impl/*.cpp
# from the Python device classes every time; without clang-format on PATH the
# rewrite is formatting-only noise, which is why the clone is left dirty there.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(git -C "$HERE" rev-parse --show-toplevel)"
VENDOR="$REPO_ROOT/vendor/ramulator2"
UPSTREAM="https://github.com/CMU-SAFARI/ramulator2"
PIN="7bead6cb7c4b03e095c6d4769ae3181a8e0bf6da"      # main, 2026-11-04 ("Visualizer improvements")
JOBS="${JOBS:-$(nproc)}"

echo "== clone / pin $PIN"
if [ ! -d "$VENDOR/.git" ]; then
    git clone "$UPSTREAM" "$VENDOR"
fi
git -C "$VENDOR" fetch --quiet origin
git -C "$VENDOR" checkout --quiet --detach "$PIN"
git -C "$VENDOR" checkout -- .                    # drop any earlier overlay edits to tracked files

echo "== overlay"
cp -r "$HERE/overlay/python" "$HERE/overlay/src" "$HERE/overlay/tests" "$VENDOR/"
git -C "$VENDOR" apply "$HERE/vendor-registration.patch"

echo "== build"
mkdir -p "$VENDOR/build"
( cd "$VENDOR/build" \
  && cmake .. -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_COMPILER="${CXX:-g++}" > cmake.log \
  && make -j"$JOBS" 2>&1 | tail -3 )

if [ "${1:-}" = "--test" ]; then
    echo "== tests"
    # shellcheck disable=SC1091
    source "$REPO_ROOT/env_python" > /dev/null 2>&1 || true
    ( cd "$VENDOR" && PYTHONPATH="$VENDOR/python" python3 -m pytest tests/smoke tests/device_timings -q )
fi
echo "ramulator2 ready: $VENDOR (PYTHONPATH=$VENDOR/python)"
