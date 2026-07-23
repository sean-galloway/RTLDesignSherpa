#!/usr/bin/env bash
# Provision a fresh Debian/Ubuntu machine to develop and SIMULATE RTL Design
# Sherpa, and install the Claude Code CLI -- one command, from nothing.
#
#   bash setup_workstation.sh                 # clone to ~/RTLDesignSherpa, sim toolchain + Claude
#   bash setup_workstation.sh --formal        # ALSO install oss-cad-suite (~2 GB: yosys/sby/iverilog)
#   bash setup_workstation.sh --dir /path     # clone somewhere other than ~/RTLDesignSherpa
#   bash setup_workstation.sh --here          # you are already inside a clone; don't clone again
#   bash setup_workstation.sh --no-claude     # skip the Claude Code CLI install
#   bash setup_workstation.sh --branch NAME   # check out a specific branch (default: main)
#
# WHAT YOU GET
#   apt packages : git, curl, build-essential, ccache, perl, python3(+venv/pip),
#                  verilator (5.020 on Ubuntu 24.04), gtkwave
#   repo         : cloned + `bin/cloud_bootstrap.sh` run (venv at repo/venv,
#                  requirements.txt incl. CocoTBFramework, one real cocotb smoke test)
#   Claude Code  : native binary at ~/.local/bin/claude (NO Node.js needed; auto-updates)
#
# REQUIREMENTS
#   - Debian 10+ / Ubuntu 20.04+ (apt). dnf/apk users: install the apt list below
#     with your package manager, then run with --here from inside a clone.
#   - sudo for the system packages.
#   - Claude Code needs 4 GB+ RAM and a paid plan (Pro/Max/Team/Enterprise/Console);
#     the free claude.ai plan does not include it.
set -euo pipefail

REPO_URL="https://github.com/sean-galloway/RTLDesignSherpa.git"
BRANCH="main"
DEST="$HOME/RTLDesignSherpa"
DO_FORMAL=0
DO_CLAUDE=1
USE_HERE=0

while [ $# -gt 0 ]; do
    case "$1" in
        --formal)    DO_FORMAL=1; shift ;;
        --no-claude) DO_CLAUDE=0; shift ;;
        --here)      USE_HERE=1; shift ;;
        --dir)       DEST="$2"; shift 2 ;;
        --branch)    BRANCH="$2"; shift 2 ;;
        --repo)      REPO_URL="$2"; shift 2 ;;
        -h|--help)   sed -n '2,33p' "$0"; exit 0 ;;
        *) echo "unknown arg: $1" >&2; exit 2 ;;
    esac
done

say()  { printf '\n\033[1m== %s\033[0m\n' "$*"; }
ok()   { printf '\033[32mok\033[0m   %s\n' "$*"; }
warn() { printf '\033[33mWARN\033[0m %s\n' "$*"; }
die()  { printf '\033[31mFAIL\033[0m %s\n' "$*"; exit 1; }

# sudo helper: use it if we are not root and it exists.
SUDO=""
if [ "$(id -u)" -ne 0 ]; then
    command -v sudo >/dev/null 2>&1 && SUDO="sudo" || die "not root and no sudo; run as root or install sudo"
fi

command -v apt-get >/dev/null 2>&1 || die "this script targets Debian/Ubuntu (apt-get not found)"

say "System packages (apt)"
# apt-get update can exit non-zero on unrelated broken third-party repos; that is
# fine as long as the install below succeeds (same trap cloud_bootstrap handles).
$SUDO apt-get update -qq || warn "apt-get update had partial failures; continuing"
$SUDO apt-get install -y -qq \
    git curl ca-certificates \
    build-essential ccache perl \
    python3 python3-venv python3-pip \
    verilator gtkwave \
    || die "apt-get install failed"
ok "base toolchain installed ($(verilator --version 2>/dev/null || echo 'verilator: check apt'))"

say "Repository"
if [ "$USE_HERE" = 1 ]; then
    REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || die "--here given but this is not a git clone"
    ok "using existing clone at $REPO_ROOT"
elif [ -d "$DEST/.git" ]; then
    REPO_ROOT="$DEST"
    ok "clone already present at $DEST"
else
    git clone --branch "$BRANCH" "$REPO_URL" "$DEST" \
        || git clone "$REPO_URL" "$DEST"   # fall back if the branch does not exist yet
    REPO_ROOT="$DEST"
    ok "cloned to $DEST"
fi

say "RTL bootstrap (venv + framework + smoke test)"
# Delegate to the repo's own bootstrap -- the single source of truth for the
# venv, requirements.txt, the pinned-Verilator handling, and the smoke test.
cd "$REPO_ROOT"
if [ "$DO_FORMAL" = 1 ]; then
    bash bin/cloud_bootstrap.sh            # full: also fetches oss-cad-suite (~2 GB)
else
    bash bin/cloud_bootstrap.sh --no-formal
fi

if [ "$DO_CLAUDE" = 1 ]; then
    say "Claude Code CLI"
    if command -v claude >/dev/null 2>&1; then
        ok "claude already installed ($(claude --version 2>/dev/null || echo present))"
    else
        # Native installer: self-contained binary, no Node.js, auto-updates.
        curl -fsSL https://claude.ai/install.sh | bash || warn "Claude install script failed; see https://code.claude.com/docs/en/setup"
        if command -v claude >/dev/null 2>&1; then
            ok "claude installed ($(claude --version 2>/dev/null || echo present))"
        else
            warn "claude not on PATH yet -- it installs to ~/.local/bin"
            case ":$PATH:" in
                *":$HOME/.local/bin:"*) : ;;
                *) warn "add this to your shell rc:  export PATH=\"\$HOME/.local/bin:\$PATH\"" ;;
            esac
        fi
    fi
fi

say "Done"
cat <<EOF

Next steps:
  cd $REPO_ROOT
  source env_python                       # activate venv + tool PATHs
  pytest val/common/test_counter_bin.py   # confirm simulation works
EOF
[ "$DO_CLAUDE" = 1 ] && cat <<'EOF'
  claude                                  # first run opens a browser to log in
                                          # (needs a Pro/Max/Team/Enterprise plan)
EOF
[ "$DO_FORMAL" = 0 ] && echo "  (re-run with --formal later if you need yosys/sby/iverilog for /formal)"
