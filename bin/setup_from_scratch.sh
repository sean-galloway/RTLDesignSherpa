#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Complete Setup From Scratch
#
# This script sets up the entire development environment on a fresh machine.
# It is idempotent — safe to run multiple times.
#
# Usage:
#   bash bin/setup_from_scratch.sh          # full setup
#   bash bin/setup_from_scratch.sh --skip-apt   # skip apt packages (no sudo)
#   bash bin/setup_from_scratch.sh --skip-formal # skip formal tools
#
# What it does:
#   1. Install system packages (verilator, yosys, etc.) via apt
#   2. Create Python venv and install requirements.txt
#   3. Install formal verification tools (sby, boolector, z3)
#   4. Run doctor check to verify everything
#
# After running:
#   source env_python        # activate environment
#   make help                # see available targets
#   make formal-check-tools  # verify formal tools

set -euo pipefail

# Parse arguments
SKIP_APT=false
SKIP_FORMAL=false
for arg in "$@"; do
    case "$arg" in
        --skip-apt)    SKIP_APT=true ;;
        --skip-formal) SKIP_FORMAL=true ;;
        --help|-h)
            echo "Usage: bash bin/setup_from_scratch.sh [--skip-apt] [--skip-formal]"
            echo ""
            echo "  --skip-apt      Skip system package installation (no sudo needed)"
            echo "  --skip-formal   Skip formal verification tools"
            exit 0
            ;;
        *) echo "Unknown argument: $arg"; exit 1 ;;
    esac
done

# Detect repo root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_ROOT"

echo "================================================================================"
echo "RTL Design Sherpa - Setup From Scratch"
echo "================================================================================"
echo "Repo root: $REPO_ROOT"
echo ""

# ==========================================================================
# Phase 1: System packages
# ==========================================================================
if [ "$SKIP_APT" = false ]; then
    echo "--- Phase 1: System packages ---"
    echo ""

    # Essential build tools
    PACKAGES=(
        build-essential
        python3
        python3-venv
        python3-pip
        git
    )

    # RTL simulation
    PACKAGES+=(
        verilator
        yosys
    )

    # Optional but useful
    PACKAGES+=(
        gtkwave
        graphviz
    )

    echo "Installing: ${PACKAGES[*]}"
    sudo apt-get update -qq
    sudo apt-get install -y -qq "${PACKAGES[@]}"
    echo ""
    echo "System packages installed."
    echo ""
else
    echo "--- Phase 1: Skipped (--skip-apt) ---"
    echo ""
fi

# ==========================================================================
# Phase 2: Python venv + requirements
# ==========================================================================
echo "--- Phase 2: Python virtual environment ---"
echo ""

if [ ! -d "$REPO_ROOT/venv" ]; then
    echo "Creating virtual environment..."
    python3 -m venv "$REPO_ROOT/venv"
else
    echo "Virtual environment already exists."
fi

echo "Upgrading pip..."
"$REPO_ROOT/venv/bin/pip" install --upgrade pip -q

echo "Installing requirements.txt..."
"$REPO_ROOT/venv/bin/pip" install -r "$REPO_ROOT/requirements.txt" -q

echo "Python environment ready."
echo ""

# ==========================================================================
# Phase 3: Formal verification tools
# ==========================================================================
if [ "$SKIP_FORMAL" = false ]; then
    echo "--- Phase 3: Formal verification tools ---"
    echo ""
    bash "$REPO_ROOT/bin/install_formal_tools.sh"
    echo ""
else
    echo "--- Phase 3: Skipped (--skip-formal) ---"
    echo ""
fi

# ==========================================================================
# Phase 4: Verify everything
# ==========================================================================
echo "--- Phase 4: Verification ---"
echo ""

# Run make doctor (doesn't need env_python for bootstrap targets)
make -C "$REPO_ROOT" doctor

echo ""
echo "================================================================================"
echo "Setup complete!"
echo "================================================================================"
echo ""
echo "Next steps:"
echo "  source env_python              # activate environment"
echo "  make help                      # see all available targets"
echo "  make test-val-common-gate      # quick smoke test"
echo "  make formal-quick              # quick formal proof"
echo ""
echo "Full test suite:"
echo "  make test-all-gate             # GATE level, all environments"
echo "  make test-all-func             # FUNC level (default)"
echo "================================================================================"
