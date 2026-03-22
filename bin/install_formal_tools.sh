#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Install formal verification tools for RTL Design Sherpa
#
# Usage:
#   bash bin/install_formal_tools.sh
#
# Installs:
#   - SymbiYosys (sby) - formal verification orchestrator (from source)
#   - Boolector - SMT solver (preferred by SVA-AXI4-FVIP)
#   - z3 - fallback SMT solver
#
# References:
#   https://symbiyosys.readthedocs.io/en/latest/install.html
#   https://github.com/YosysHQ/sby

set -euo pipefail

INSTALL_DIR="${FORMAL_TOOLS_DIR:-/tmp/formal_tools_build}"
OSS_CAD_DIR="${OSS_CAD_SUITE_DIR:-/mnt/data/tools/oss-cad-suite}"

echo "================================================================================"
echo "Installing Formal Verification Tools"
echo "================================================================================"

# --------------------------------------------------------------------------
# Option A: Use OSS CAD Suite (recommended — matched tool versions)
# --------------------------------------------------------------------------
if [ -d "$OSS_CAD_DIR/bin" ]; then
    echo "OSS CAD Suite found at $OSS_CAD_DIR"
    echo "  yosys: $($OSS_CAD_DIR/bin/yosys --version 2>/dev/null | head -1)"
    echo "  sby:   $($OSS_CAD_DIR/bin/sby --version 2>/dev/null | head -1)"
    echo ""
    echo "Add to your env_python or shell:"
    echo "  export PATH=\"$OSS_CAD_DIR/bin:\$PATH\""
    echo ""
    echo "Formal tools ready via OSS CAD Suite."
    echo "================================================================================"
    exit 0
fi

echo "OSS CAD Suite not found at $OSS_CAD_DIR"
echo "Falling back to individual tool installation..."
echo ""

# --------------------------------------------------------------------------
# Check prerequisites
# --------------------------------------------------------------------------
if ! command -v yosys &>/dev/null; then
    echo "ERROR: yosys not found. Install via package manager first:"
    echo "  sudo apt-get install yosys"
    exit 1
fi
echo "yosys: $(yosys --version 2>/dev/null | head -1)"

if ! command -v python3 &>/dev/null; then
    echo "ERROR: python3 not found."
    exit 1
fi

# Ensure click is available (sby dependency)
python3 -c "import click" 2>/dev/null || pip3 install click

# --------------------------------------------------------------------------
# Install SymbiYosys (sby) from source
# --------------------------------------------------------------------------
echo ""
echo "--- Installing SymbiYosys (sby) ---"
if command -v sby &>/dev/null; then
    echo "sby already installed: $(sby --version 2>/dev/null | head -1)"
else
    echo "Installing sby from source (https://github.com/YosysHQ/sby)..."
    mkdir -p "$INSTALL_DIR"
    if [ -d "$INSTALL_DIR/sby" ]; then
        echo "  Updating existing clone..."
        cd "$INSTALL_DIR/sby" && git pull && cd -
    else
        git clone https://github.com/YosysHQ/sby.git "$INSTALL_DIR/sby"
    fi
    cd "$INSTALL_DIR/sby"
    sudo make install
    cd -
    if command -v sby &>/dev/null; then
        echo "sby installed successfully: $(sby --version 2>/dev/null | head -1)"
    else
        echo "ERROR: sby installation failed. Check output above."
        echo "  Manual install: cd $INSTALL_DIR/sby && sudo make install"
    fi
fi

# --------------------------------------------------------------------------
# Install Boolector SMT solver
# --------------------------------------------------------------------------
echo ""
echo "--- Installing Boolector ---"
if command -v boolector &>/dev/null; then
    echo "boolector already installed"
else
    echo "Attempting to install boolector..."

    # Try apt first (fastest)
    if sudo apt-get install -y boolector 2>/dev/null; then
        echo "boolector installed via apt"
    else
        echo "apt package not available. Building from source..."
        mkdir -p "$INSTALL_DIR"
        if [ ! -d "$INSTALL_DIR/boolector" ]; then
            git clone https://github.com/boolector/boolector.git "$INSTALL_DIR/boolector"
        fi
        cd "$INSTALL_DIR/boolector"
        # Boolector requires lingeling or CaDiCaL SAT solver
        ./contrib/setup-cadical.sh
        ./contrib/setup-btor2tools.sh
        ./configure.sh
        cd build && make -j"$(nproc)"
        sudo cp bin/boolector /usr/local/bin/
        cd -
        echo "boolector built and installed to /usr/local/bin/"
    fi

    if command -v boolector &>/dev/null; then
        echo "boolector: OK"
    else
        echo "WARNING: Could not install boolector."
        echo "  Build manually: https://github.com/boolector/boolector"
        echo "  Or use z3 as fallback (change .sby files: smtbmc z3)"
    fi
fi

# --------------------------------------------------------------------------
# Install z3 SMT solver (fallback)
# --------------------------------------------------------------------------
echo ""
echo "--- Installing z3 (fallback solver) ---"
if command -v z3 &>/dev/null; then
    echo "z3 already installed: $(z3 --version 2>/dev/null)"
else
    echo "Attempting to install z3..."
    # Try apt first, then pip
    if sudo apt-get install -y z3 2>/dev/null; then
        echo "z3 installed via apt"
    elif pip3 install z3-solver 2>/dev/null; then
        echo "z3 installed via pip (z3-solver)"
    else
        echo "WARNING: Could not install z3."
        echo "  Try: sudo apt-get install z3"
        echo "  Or:  pip3 install z3-solver"
    fi
fi

# --------------------------------------------------------------------------
# Summary
# --------------------------------------------------------------------------
echo ""
echo "================================================================================"
echo "Summary"
echo "================================================================================"
echo -n "  yosys:     "; command -v yosys &>/dev/null && echo "OK ($(yosys --version 2>/dev/null | head -1))" || echo "MISSING"
echo -n "  sby:       "; command -v sby &>/dev/null && echo "OK ($(sby --version 2>/dev/null | head -1))" || echo "MISSING"
echo -n "  boolector: "; command -v boolector &>/dev/null && echo "OK" || echo "MISSING"
echo -n "  z3:        "; command -v z3 &>/dev/null && echo "OK (optional)" || echo "MISSING (optional)"
echo ""
echo "Build artifacts in: $INSTALL_DIR"
echo "  (safe to delete after successful install)"
echo ""
echo "Next steps:"
echo "  make formal-check-tools       # Verify installation"
echo "  make formal-quick             # Run quick proof (~seconds)"
echo "  make formal-common            # Run all building block proofs"
echo "================================================================================"
