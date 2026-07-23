#!/usr/bin/env bash
# Provision a fresh sandbox (Claude cloud, Codespace, CI runner) to run RTL
# Design Sherpa simulations and Kimi review batches.
#
#   bash bin/cloud_bootstrap.sh
#   source env_python
#
# WHY THIS EXISTS: env_python assumes a workstation that has been hand-built
# over time -- a venv at $REPO_ROOT/venv, Verilator under /mnt/data/tools,
# oss-cad-suite, Verible, an editable checkout of RTLDesignSherpa-DV. A sandbox
# has none of that. This script builds the subset needed for simulation and
# review, and is explicit about what it CANNOT provide.
#
# env_python itself needs no changes: its tool paths are either guarded by
# `if [ -d ]` or are harmless PATH prepends of directories that do not exist,
# so it falls through to whatever this script installed. The one hard
# requirement it has is that $REPO_ROOT/venv exists -- which is the main thing
# we create here.
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

# Verilator is PINNED at 5.020. Newer releases have cocotb VCD/FST generation
# bugs that surface as corrupt or empty waves, not as an error -- so a silent
# upgrade costs a debugging session before anyone suspects the simulator.
# Ubuntu 24.04 ships exactly 5.020-1, which is why apt is the right source here.
WANT_VERILATOR="5.020"

say()  { printf '\n\033[1m== %s\033[0m\n' "$*"; }
warn() { printf '\033[33mWARN\033[0m %s\n' "$*"; }
ok()   { printf '\033[32mok\033[0m   %s\n' "$*"; }

say "System packages"
if command -v verilator >/dev/null 2>&1; then
    ok "verilator already present: $(verilator --version)"
else
    if ! command -v apt-get >/dev/null 2>&1; then
        warn "no apt-get; install Verilator $WANT_VERILATOR manually"
    else
        sudo apt-get update -qq
        # git/perl/ccache are Verilator runtime deps; gtkwave is for wave dumps.
        sudo apt-get install -y -qq verilator build-essential ccache perl python3-venv
        ok "installed $(verilator --version)"
    fi
fi

if command -v verilator >/dev/null 2>&1; then
    HAVE="$(verilator --version | awk '{print $2}')"
    if [ "$HAVE" != "$WANT_VERILATOR" ]; then
        warn "Verilator $HAVE != pinned $WANT_VERILATOR."
        warn "Waves may be silently corrupt. Build 5.020 from source if tests misbehave."
    else
        ok "Verilator $HAVE matches the pin"
    fi
fi

say "Python venv"
if [ ! -d venv ]; then
    python3 -m venv venv
    ok "created $REPO_ROOT/venv"
else
    ok "venv already exists"
fi
./venv/bin/pip install -q --upgrade pip setuptools wheel
./venv/bin/pip install -q -r requirements.txt
ok "requirements.txt installed"

say "Verification framework"
# Locally this is an editable install of a sibling checkout. In a sandbox there
# is no sibling checkout, so it comes from PyPI -- which is precisely why the
# requirements.txt pin has to be a version that actually exists there.
./venv/bin/python - <<'PY'
import sys
try:
    import CocoTBFramework as f
    print(f"ok   CocoTBFramework {f.__version__} (from PyPI)")
except Exception as e:
    sys.exit(f"FAIL CocoTBFramework did not import: {e}")
PY

say "Smoke test"
# One real cocotb+Verilator run. If this passes, the simulation path is good;
# if it fails, nothing downstream is worth debugging yet.
set +e
( source env_python >/dev/null 2>&1
  cd val/common
  REG_LEVEL=GATE python3 -m pytest test_counter_bin.py -x -q --no-header 2>&1 | tail -5 )
SMOKE=$?
set -e
[ $SMOKE -eq 0 ] && ok "simulation works" || warn "smoke test failed (exit $SMOKE) -- see output above"

say "Not available in this sandbox"
for t in vivado yosys sby sv2v verible-verilog-lint; do
    command -v "$t" >/dev/null 2>&1 && ok "$t present" || warn "$t missing"
done
cat <<'EOF'

  vivado                 FPGA builds and board runs. Licensed, ~100 GB, and the
                         boards are on a desk -- cloud cannot do these at all.
  yosys / sby / sv2v     formal (oss-cad-suite). Installable via the upstream
                         tarball if you need /formal; not fetched here because
                         it is ~2 GB and simulation does not need it.
  verible-verilog-lint   style lint only. Optional.

  Simulation, pytest, doc generation and Kimi review batches all work without
  any of the above.
EOF

say "Kimi review endpoint"
cat <<'EOF'
  The local litellm proxy on localhost:4000 does not exist here, so the review
  scripts must talk to Moonshot directly. Export these before running a batch:

    export KIMI_BASE_URL=https://api.moonshot.ai/v1
    export KIMI_API_KEY=<MOONSHOT_API_KEY>     # never commit this
    export KIMI_MODEL=kimi-k2-0711-preview     # a real model id, not the alias

  Then:
    python3 bin/build_review_bundle.py /tmp/review
    python3 bin/review/run_batch.py qc --books /tmp/review/books \
        --results /tmp/review/results --dry-run

  Sandbox egress may be filtered -- if the first call hangs or 403s, the host
  needs api.moonshot.ai allowlisted.
EOF

say "Done"
echo "Next:  source env_python"
